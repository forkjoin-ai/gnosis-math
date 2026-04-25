
namespace Gnosis

def pipelineTerminal (current : List BranchSnapshot) : List (List BranchSnapshot) -> List BranchSnapshot
  | [] => current
  | next :: rest => pipelineTerminal next rest

