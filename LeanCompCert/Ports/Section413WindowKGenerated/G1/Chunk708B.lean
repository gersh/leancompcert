import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk708A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk708B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk708A

def state06 : KState := ⟨⟨362473950779216183, 362474025367847864⟩, ⟨794049057782542873, 797618542082519005⟩, true⟩

def words05 : List Nat := [371285282979651690, 371285282740368992, 371285282500127387, 371285282459797880, 371285282345216163, 371285282265167662, 371285282184289995, 371285282103516106, 371285281783136745, 371285281627261956]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470556128047659, 362470630738339712⟩, ⟨1034599287471402819, 1038170306737146005⟩, true⟩

def words06 : List Nat := [371285281470088022, 371285281378101349, 371285281106718600, 371285280821554775, 371285280535436014, 371285280310848100, 371285280002772908, 371285279894477261, 371285279785341399, 371285279677336991]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485246619938787, 362485321252192198⟩, ⟨(-6615925020906117), (-3043349243608785)⟩, true⟩

def words07 : List Nat := [371285279472285406, 371285279447281416, 371285279438187248, 371285279440615288, 371285279194596685, 371285278900011075, 371285278604452084, 371285278508627336, 371285278312786020, 371285278316155128]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475695785463102, 362475770439653833⟩, ⟨670416858380941793, 673990989186784039⟩, true⟩

def words08 : List Nat := [371285278319003470, 371285278321474855, 371285278223294462, 371285278265209448, 371285278366440688, 371285278368873039, 371285278274728971, 371285278181883537, 371285278088072101, 371285278000511314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464504382964284, 362464579058991197⟩, ⟨1463899958244143344, 1467475637129132298⟩, true⟩

def words09 : List Nat := [371285277932541246, 371285277999652321, 371285278065533934, 371285278067962869, 371285277868754824, 371285277678362013, 371285277486632727, 371285277461605557, 371285277171024500, 371285276881799789]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk708B
