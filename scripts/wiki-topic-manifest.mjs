#!/usr/bin/env node
import { mkdir, readFile, readdir, stat, writeFile } from "node:fs/promises";
import path from "node:path";

const packageRoot = path.resolve(import.meta.dirname, "..");
const topicPath = path.join(packageRoot, "docs", "WIKI_TOPICS.md");
const outputDir = path.join(packageRoot, "docs", "generated");
const manifestPath = path.join(outputDir, "wiki-topic-manifest.json");
const rejectedPath = path.join(outputDir, "wiki-topic-rejections.json");
const generationListPath = path.join(outputDir, "wiki-generation-list.md");
const stopWords = new Set([
  "core",
  "finite",
  "gnosis",
  "lean",
  "local",
  "math",
  "page",
  "science",
  "surface",
  "theorem",
  "theory",
  "topic",
]);
const candidateAliases = new Map([
  ["mythology", ["myth", "witness", "folklore", "epic", "ritual"]],
  ["spiritualism", ["spiritual", "spirit", "pneuma", "religious", "witness"]],
  ["religious-topology", ["spiritual-topology", "spiritual", "topological"]],
  ["gnosticism", ["gnostic", "esoteric", "witness"]],
  ["hermeticism", ["hermetic", "esoteric", "witness"]],
  ["religion", ["religious", "interfaith", "scriptural", "witness"]],
  ["topology", ["topological", "homology", "manifold", "knot", "braid"]],
]);

const args = new Map();
for (let index = 2; index < process.argv.length; index += 1) {
  const arg = process.argv[index];
  if (!arg.startsWith("--")) {
    continue;
  }
  const [key, inlineValue] = arg.slice(2).split("=", 2);
  const nextValue = process.argv[index + 1];
  if (inlineValue !== undefined) {
    args.set(key, inlineValue);
  } else if (nextValue && !nextValue.startsWith("--")) {
    args.set(key, nextValue);
    index += 1;
  } else {
    args.set(key, "true");
  }
}

function slugify(value) {
  return value
    .toLowerCase()
    .replace(/`/g, "")
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "");
}

function words(value) {
  return new Set(
    value
      .toLowerCase()
      .replace(/`[^`]+`/g, " ")
      .split(/[^a-z0-9]+/)
      .filter((word) => word.length >= 3 && !stopWords.has(word)),
  );
}

function titleCaseFromModule(modulePath) {
  const baseName = path.basename(modulePath, ".lean");
  return baseName
    .replace(/([a-z0-9])([A-Z])/g, "$1 $2")
    .replace(/([A-Z]+)([A-Z][a-z])/g, "$1 $2")
    .replace(/\s+/g, " ")
    .trim();
}

function moduleToTopicTitle(modulePath) {
  return titleCaseFromModule(modulePath).replace(/\s+/g, " ").trim();
}

function moduleRows(paths) {
  return paths.map(
    (modulePath) =>
      `| ${moduleToTopicTitle(modulePath)} | \`${modulePath}\` | module-derived |`,
  );
}

async function walkFiles(directory) {
  const entries = await readdir(directory, { withFileTypes: true });
  const files = [];
  await Promise.all(
    entries.map(async (entry) => {
      const fullPath = path.join(directory, entry.name);
      if (entry.isDirectory()) {
        files.push(...(await walkFiles(fullPath)));
        return;
      }
      files.push(fullPath);
    }),
  );
  return files;
}

async function pathExists(filePath) {
  try {
    await stat(filePath);
    return true;
  } catch {
    return false;
  }
}

function extractInlineCode(value) {
  return [...value.matchAll(/`([^`]+)`/g)].map((match) => match[1]);
}

function parseTopicTables(markdown) {
  const lines = markdown.split(/\r?\n/);
  const topics = [];
  let currentSection = "Uncategorized";

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    const heading = line.match(/^##\s+(.+)$/);
    if (heading) {
      currentSection = heading[1].trim();
      continue;
    }

    if (!line.startsWith("|") || line.includes("---")) {
      continue;
    }

    const cells = line
      .slice(1, -1)
      .split("|")
      .map((cell) => cell.trim());

    if (cells.length < 3 || cells[0] === "Page" || cells[0] === "Page cluster") {
      continue;
    }

    const [title, anchorText, generationAngle] = cells;
    topics.push({
      title,
      slug: slugify(title),
      section: currentSection,
      localAnchors: extractInlineCode(anchorText),
      anchorText,
      generationAngle,
    });
  }

  const backlog = [];
  let inBacklog = false;
  for (const line of lines) {
    if (line === "## Generation Backlog") {
      inBacklog = true;
      continue;
    }
    if (inBacklog && line.startsWith("## ")) {
      break;
    }
    const item = line.match(/^\d+\.\s+(.+)$/);
    if (inBacklog && item) {
      backlog.push(item[1].trim());
    }
  }

  return { topics, backlog };
}

function resolveAnchor(anchor, modulePaths) {
  if (anchor.endsWith("/*")) {
    const prefix = anchor.slice(0, -1);
    const matches = modulePaths.filter((modulePath) => modulePath.startsWith(prefix));
    return { anchor, status: matches.length > 0 ? "matched-glob" : "missing", matches };
  }

  if (anchor.includes("*")) {
    const pattern = new RegExp(`^${anchor.split("*").map(escapeRegExp).join(".*")}$`);
    const matches = modulePaths.filter((modulePath) => pattern.test(modulePath));
    return { anchor, status: matches.length > 0 ? "matched-glob" : "missing", matches };
  }

  const matches = modulePaths.includes(anchor) ? [anchor] : [];
  return { anchor, status: matches.length > 0 ? "matched" : "missing", matches };
}

function escapeRegExp(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function scoreCandidate(candidate, topic) {
  const candidateWords = words(candidate.title);
  const candidateSlug = slugify(candidate.title);
  const slugAliases = candidateAliases.get(candidateSlug);
  if (slugAliases) {
    for (const alias of slugAliases) {
      candidateWords.add(alias);
    }
  }
  for (const word of [...candidateWords]) {
    const aliases = candidateAliases.get(word);
    if (!aliases) {
      continue;
    }
    for (const alias of aliases) {
      candidateWords.add(alias);
    }
  }
  const topicWords = words(
    `${topic.title} ${topic.generationAngle} ${topic.anchors
      .flatMap((anchor) => [anchor.anchor, ...anchor.matches])
      .join(" ")}`,
  );
  let overlap = 0;
  for (const word of candidateWords) {
    if (topicWords.has(word)) {
      overlap += 1;
    }
  }

  const exactSlugMatch = slugify(candidate.title) === topic.slug;
  const topicSlug = topic.slug;
  const containmentMatch =
    candidateSlug.includes(topicSlug) || topicSlug.includes(candidateSlug);
  return overlap + (exactSlugMatch ? 3 : 0) + (containmentMatch ? 2 : 0);
}

async function readCandidates(candidatesPath) {
  if (!candidatesPath) {
    return [];
  }

  const absolutePath = path.resolve(process.cwd(), candidatesPath);
  const text = await readFile(absolutePath, "utf8");
  if (candidatesPath.endsWith(".json")) {
    const parsed = JSON.parse(text);
    if (!Array.isArray(parsed)) {
      throw new Error(`Expected JSON array in ${candidatesPath}`);
    }
    return parsed.map((candidate) =>
      typeof candidate === "string" ? { title: candidate } : candidate,
    );
  }

  return text
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean)
    .map((title) => ({ title }));
}

const topicMarkdown = await readFile(topicPath, "utf8");
const { topics, backlog } = parseTopicTables(topicMarkdown);
const files = await walkFiles(path.join(packageRoot, "Gnosis"));
const modulePaths = files
  .filter((file) => file.endsWith(".lean"))
  .map((file) => path.relative(packageRoot, file).replaceAll(path.sep, "/"))
  .sort();
const markdownAnchors = [
  "README.md",
  "ROADMAP.md",
  "GAP_CLOSURE.md",
  "VOID_AS_MEDIUM.md",
  "HFT_CONTRACTS.md",
];
const anchorPaths = new Set([...modulePaths, ...markdownAnchors]);
const manifestTopics = topics.map((topic) => {
  const resolvedAnchors = topic.localAnchors.map((anchor) =>
    resolveAnchor(anchor, [...anchorPaths]),
  );
  const matchedAnchorCount = resolvedAnchors.filter((anchor) => anchor.status !== "missing").length;
  const missingAnchorCount = resolvedAnchors.length - matchedAnchorCount;
  const backlogRank = backlog.findIndex(
    (item) => slugify(item) === topic.slug || slugify(item).includes(topic.slug),
  );
  const readiness =
    matchedAnchorCount > 0 && missingAnchorCount === 0
      ? "ready"
      : matchedAnchorCount > 0
        ? "needs-anchor-review"
        : "blocked";

  return {
    title: topic.title,
    slug: topic.slug,
    section: topic.section,
    readiness,
    backlogRank: backlogRank >= 0 ? backlogRank + 1 : null,
    generationAngle: topic.generationAngle,
    anchors: resolvedAnchors,
  };
});

const dumpCandidates = await readCandidates(args.get("candidates"));
const acceptedDumpCandidates = [];
const rejectedDumpCandidates = [];
for (const candidate of dumpCandidates) {
  const scores = manifestTopics
    .map((topic) => ({
      topic: topic.title,
      slug: topic.slug,
      score: scoreCandidate(candidate, topic),
    }))
    .filter((match) => match.score > 0)
    .sort((left, right) => {
      if (right.score !== left.score) {
        return right.score - left.score;
      }
      const leftIsAtlas = left.slug.endsWith("-atlas") ? 1 : 0;
      const rightIsAtlas = right.slug.endsWith("-atlas") ? 1 : 0;
      if (leftIsAtlas !== rightIsAtlas) {
        return leftIsAtlas - rightIsAtlas;
      }
      return right.slug.length - left.slug.length;
    })
    .slice(0, 5);

  if (scores.length === 0) {
    rejectedDumpCandidates.push({
      title: candidate.title,
      reason: "no local module or topic-word match",
    });
    continue;
  }

  acceptedDumpCandidates.push({
    title: candidate.title,
    matches: scores,
  });
}

const manifest = {
  generatedAt: new Date().toISOString(),
  packageRoot: "open-source/gnosis-math",
  source: "docs/WIKI_TOPICS.md",
  moduleCount: modulePaths.length,
  topicCount: manifestTopics.length,
  readyCount: manifestTopics.filter((topic) => topic.readiness === "ready").length,
  needsAnchorReviewCount: manifestTopics.filter(
    (topic) => topic.readiness === "needs-anchor-review",
  ).length,
  blockedCount: manifestTopics.filter((topic) => topic.readiness === "blocked").length,
  dumpCandidateCount: dumpCandidates.length,
  acceptedDumpCandidateCount: acceptedDumpCandidates.length,
  topics: manifestTopics,
  acceptedDumpCandidates,
};

const topologyPattern =
  /topolog|homolog|cohomolog|manifold|covering|fiber|fibration|braid|knot|cobord|homotop|sheaf|langlands|geometry|geometric/i;
const spiritualPattern =
  /spirit|spiritual|pneuma|relig|bible|gnostic|hermetic|hindu|buddhist|tao|islam|manda|manicha|interfaith|holy|god|soul|prana|witnesses|witness/i;
const topologyModules = modulePaths.filter((modulePath) => topologyPattern.test(modulePath));
const spiritualModules = modulePaths.filter((modulePath) => spiritualPattern.test(modulePath));
const topologySet = new Set(topologyModules);
const spiritualOnlyModules = spiritualModules.filter((modulePath) => !topologySet.has(modulePath));
const generationList = [
  "# Gnosis Math Wiki Generation List",
  "",
  "Parent: [Generated Gnosis Math Docs](./README.md)",
  "",
  "This is the concrete page queue generated from `docs/WIKI_TOPICS.md` and",
  "local `Gnosis/**/*.lean` modules. Topology and spiritual/witness surfaces",
  "are in scope when the listed module can prove, disprove, or bound the claim.",
  "",
  "## Counts",
  "",
  `- Atlas topics: ${manifestTopics.length}`,
  `- Topology-derived modules: ${topologyModules.length}`,
  `- Spiritual/witness-derived modules excluding topology duplicates: ${spiritualOnlyModules.length}`,
  "",
  "## Atlas Topics",
  "",
  "| Page | Slug | Readiness |",
  "|------|------|-----------|",
  ...manifestTopics.map(
    (topic) => `| ${topic.title} | \`${topic.slug}\` | ${topic.readiness} |`,
  ),
  "",
  "## Topology-Derived Pages",
  "",
  "| Page | Local anchor | Source |",
  "|------|--------------|--------|",
  ...moduleRows(topologyModules),
  "",
  "## Spiritual And Witness-Derived Pages",
  "",
  "| Page | Local anchor | Source |",
  "|------|--------------|--------|",
  ...moduleRows(spiritualOnlyModules),
  "",
].join("\n");

await mkdir(outputDir, { recursive: true });
await writeFile(manifestPath, `${JSON.stringify(manifest, null, 2)}\n`);
await writeFile(generationListPath, `${generationList}\n`);
await writeFile(
  rejectedPath,
  `${JSON.stringify(
    {
      generatedAt: manifest.generatedAt,
      rejectedDumpCandidateCount: rejectedDumpCandidates.length,
      rejectedDumpCandidates,
    },
    null,
    2,
  )}\n`,
);

console.log(
  JSON.stringify(
    {
      manifest: path.relative(packageRoot, manifestPath),
      generationList: path.relative(packageRoot, generationListPath),
      rejections: path.relative(packageRoot, rejectedPath),
      moduleCount: manifest.moduleCount,
      topicCount: manifest.topicCount,
      readyCount: manifest.readyCount,
      needsAnchorReviewCount: manifest.needsAnchorReviewCount,
      blockedCount: manifest.blockedCount,
      dumpCandidateCount: manifest.dumpCandidateCount,
      acceptedDumpCandidateCount: manifest.acceptedDumpCandidateCount,
    },
    null,
    2,
  ),
);
