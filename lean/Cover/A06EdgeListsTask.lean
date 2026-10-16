import Cover.InputSerializationTasks

namespace Cover.A06

/-- Each edge's canonical sorted index list is constructed by the actual stepped
    finite scan, rather than calling Finset.sort before scalar-task execution. -/
def edgeListsTask (I : Input) : FinTask (List (List (Fin I.design.groups))) :=
  FinTask.mapTask InputTasks.edgeIndicesTask I.design.edges

@[simp] theorem edgeListsTask_result (I : Input) : (edgeListsTask I).result = edgeLists I := by
  simp [edgeListsTask,InputTasks.edgeIndicesTask_result,edgeLists]

end Cover.A06
