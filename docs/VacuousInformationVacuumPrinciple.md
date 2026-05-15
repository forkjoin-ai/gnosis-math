# Vacuous Information Vacuum Principle

Parent: [Gnosis Math](../README.md)

## Claim

Vacuous information should not receive attention energy. It should either
resolve into useful work/truth, or pay debt.

The Skyrms energy-tax surface formalizes this as a runtime settlement rule:
attention mass is not the taxable property. Harmful externality is.

```text
taxed:
  unresolved debt
  failed attention
  routing waste
  congestion

rebated:
  useful work
  truthful closure
  scarce semantic coverage
  successful attention
```

This is the precise version of the contrarian rule: dominant attention can be
innocent. A head that receives or routes a lot of attention is not guilty by
being large. It becomes taxable only when it leaves unresolved semantic debt,
fails verification, congests the route, or stays off-shell.

## Vacuum Reading

The vacuum is not emptiness as nothing. It is an unpaid obligation in the
semantic field.

```text
truth / useful work / verified closure
  = vacuum filled

failed attention / unresolved claim / hallucinated path
  = vacuum left open

tax
  = carrying cost of the open vacuum

rebate
  = reward for closing it
```

For LLM attention, this is anti-hallucinatory because hallucination is treated
as debt-bearing attention. A head that opens a claim without closing it has not
created value; it has created vacuum pressure. The tax prevents that pressure
from masquerading as useful signal.

## Attachment Reading

This can be read as a computational analogue of Buddhist attachment, not as a
claim about Buddhism itself.

In that reading, attachment is persistent attention to an object after that
object has stopped resolving uncertainty, truth, or useful work. The object may
be a token path, a latent hypothesis, a head-local attractor, or a stale
semantic route. The problem is not that attention becomes large. The problem is
that attention clings while leaving debt open.

```text
attachment
  = attention persisting on unresolved representation

non-attachment
  = release, reroute, verify, or pay debt

dukkha-like computational cost
  = accumulated unresolved debt and failed attention

right attention
  = rebated attention that closes uncertainty or performs useful work
```

This is why the settlement should be soft before it is punitive. The first
practical implementation should adjust attention energy through multipliers:
paths that keep unresolved vacuum open become more expensive; paths that close
the vacuum become easier to route through. That gives the model a pressure
toward release without brittle suppression.

## Formal Anchors

The core settlement is in `Gnosis.SkyrmsEnergyTax`.

Key theorem surfaces:

- `skyrms_tax_is_minimal_complete_gate`
- `optimal_admissible_energy_gate_statement`
- `successful_swarm_attempt_strictly_lowers_tax_vs_failure`
- `successful_swarm_attempt_strictly_raises_rebate_weight_vs_failure`

The contrarian witness is in
`Gnosis.Contrarian.ContrarianDominantAttentionIsInnocent`.

Key theorem surfaces:

- `dominant_attention_with_zero_externality_pays_floor`
- `harmful_externality_tax_exceeds_clean_dominance`
- `contrarian_dominant_attention_is_innocent`

Together they state:

```text
High attention mass is not the taxable offense.
Positive harmful externality is.
```

## Runtime Mirror

The Rust runtime mirror lives in
`open-source/gnosis/distributed-inference/src/skyrms_energy_tax.rs`.

It implements:

- `EnergyNode`
- `skyrms_tax`
- `rebate_weight`
- `proportional_rebate`
- `settle_energy_network`
- `settlement_multiplier`
- `apply_head_multipliers_in_place`

The first bridge into existing inference code is
`attention_market::head_state_energy_node`, which maps attention-market
`HeadState` rows into the Skyrms settlement ledger:

```text
on-shell head:
  useful_work = 1
  truth_score = 1
  failed_attention = 0

off-shell head:
  failed_attention = 1
  unresolved_debt = mesh residual

zero-balance head:
  congestion_load = 1
```

The runtime controller should remain soft at first: use settlement multipliers
to scale head-major attention output, not to prune heads or mutate weights.

```text
net positive settlement -> multiplier > 1.0
net negative settlement -> multiplier < 1.0
```

That makes the vacuum principle measurable without making the model brittle.
