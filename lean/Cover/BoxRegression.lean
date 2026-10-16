import Cover.BoxTasks
import Cover.Regression

namespace Cover.Regression

def boxChecks : List Bool := [
  decide ((FinTask.run 100 (splitStoredTask (StoredBox.unit (n:=1)) 0 false)).map
    (fun c => c.val.view 0) = some (⟨0,1/2⟩ : QInterval)),
  decide ((FinTask.run 100 (splitStoredTask (StoredBox.unit (n:=1)) 0 true)).map
    (fun c => c.val.view 0) = some (⟨1/2,1⟩ : QInterval)),
  decide ((FinTask.run 200 (splitStoredTask (StoredBox.unit (n:=2)) 1 true)).map
    (fun c => c.val.view 0) = some (⟨0,1⟩ : QInterval)),
  decide (FinTask.run 1000 (stageStoredTask (coeff 1) constraint objective (by decide) 1) =
    some (.success sampleTree)),
  decide (FinTask.run 1000 (checkTreeStoredTask (coeff 1) constraint objective 1 .unit sampleTree) = some true)]

#eval do
  if boxChecks.all id then IO.println "All 5 stored-box split/generator/replay regressions passed."
  else throw (IO.userError "Stored-box regression failed.")

end Cover.Regression
