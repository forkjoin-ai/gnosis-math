import Init

namespace Gnosis.Witnesses.Bible.FirstCorinthians
namespace FirstCorinthiansOrdinancesSupperWitness

/-! # 1 Corinthians 11 -- Ordinances, Headship, and the Lord's Supper
Source text: `docs/ebooks/source-texts/bible-kjv.txt:92250-92349`. -/

structure OrdinancesSupper where
  followAsPaulFollowsChrist : Bool
  rememberAndKeepOrdinances : Bool
  headshipOrderNamed : Bool
  prayingProphesyingHonorDishonor : Bool
  neitherWithoutOtherInLord : Bool
  divisionsAtAssembly : Bool
  lordSupperReceivedAndDelivered : Bool
  breadCupRemembranceAndProclamation : Bool
  examineSelfDiscernBody : Bool
  judgeOurselvesAvoidJudgment : Bool
deriving DecidableEq, Repr

def ordinancesSupper : OrdinancesSupper where
  followAsPaulFollowsChrist := true
  rememberAndKeepOrdinances := true
  headshipOrderNamed := true
  prayingProphesyingHonorDishonor := true
  neitherWithoutOtherInLord := true
  divisionsAtAssembly := true
  lordSupperReceivedAndDelivered := true
  breadCupRemembranceAndProclamation := true
  examineSelfDiscernBody := true
  judgeOurselvesAvoidJudgment := true

theorem first_corinthians_ordinances_supper_witness :
    ordinancesSupper.followAsPaulFollowsChrist = true
    ∧ ordinancesSupper.rememberAndKeepOrdinances = true
    ∧ ordinancesSupper.headshipOrderNamed = true
    ∧ ordinancesSupper.prayingProphesyingHonorDishonor = true
    ∧ ordinancesSupper.neitherWithoutOtherInLord = true
    ∧ ordinancesSupper.divisionsAtAssembly = true
    ∧ ordinancesSupper.lordSupperReceivedAndDelivered = true
    ∧ ordinancesSupper.breadCupRemembranceAndProclamation = true
    ∧ ordinancesSupper.examineSelfDiscernBody = true
    ∧ ordinancesSupper.judgeOurselvesAvoidJudgment = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FirstCorinthiansOrdinancesSupperWitness
end Gnosis.Witnesses.Bible.FirstCorinthians
