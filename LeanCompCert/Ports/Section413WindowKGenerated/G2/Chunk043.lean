import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk043

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360718725163257156, 360718725255317234⟩, ⟨(-614522745084744652), (-614522476231893240)⟩, true⟩

def state01 : KState := ⟨⟨360596464621261035, 360596464713772393⟩, ⟨(-89023545704016030), (-89023274908419332)⟩, true⟩

def words00 : List Nat := [360575849382540993, 360575881207490043, 360575925285059518, 360575969342160476, 360575969342205252, 360575958553709074, 360575894756285456, 360575857496959483, 360575820254913543, 360575814452833303]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360434136825587952, 360434136918557098⟩, ⟨611673297314733532, 611673570085709424⟩, true⟩

def words01 : List Nat := [360575814452876416, 360575792409902102, 360575770377139422, 360575790520083717, 360575799873680616, 360575809222952123, 360575809222994921, 360575790859587428, 360575760805995862, 360575728022743605]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360357905785657494, 360357905879079634⟩, ⟨940441662047727529, 940441936777936963⟩, true⟩

def words02 : List Nat := [360575695254649287, 360575684711621724, 360575621626477826, 360575517009511753, 360575412440915687, 360575291717685320, 360575213576847794, 360575188373292121, 360575163181375888, 360575098012284701]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360794909483923272, 360794909577800830⟩, ⟨(-955285045495072357), (-955284768790638861)⟩, true⟩

def words03 : List Nat := [360575047864059364, 360575024346141094, 360575000839064784, 360574974794051340, 360574943595066327, 360574861158482678, 360574778759905433, 360574749036172040, 360574797879872151, 360574848585220633]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360730470762927455, 360730470857264595⟩, ⟨(-677155438092753788), (-677155159391472390)⟩, true⟩

def words04 : List Nat := [360574871933145744, 360574884416532590, 360574921571719795, 360574958709818394, 360574958709859128, 360574958445229266, 360574938954588068, 360574876151672819, 360574813377630014, 360574838782019486]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360452916246906630, 360452916341699730⟩, ⟨532387515665339085, 532387796352377783⟩, true⟩

def words05 : List Nat := [360574893083975447, 360574947360991385, 360574974505066922, 360575005388849542, 360575005388890306, 360575003753726805, 360575052667144100, 360575052667192557, 360575051647075743, 360575023634441102]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360718745986711471, 360718746081963168⟩, ⟨(-628278792301765386), (-628278509612997900)⟩, true⟩

def words06 : List Nat := [360574995634643268, 360574960254420082, 360574995218195628, 360575038704234358, 360575038704279426, 360575033835710479, 360575011451861878, 360574994703119648, 360574977962029576, 360575008147940520]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360721684500370433, 360721684596084749⟩, ⟨(-641200224048203895), (-641199939335467743)⟩, true⟩

def words07 : List Nat := [360575009492240733, 360575010835931410, 360575063982040597, 360575143232290137, 360575186861092094, 360575230469965769, 360575247332815449, 360575258485157475, 360575291915815904, 360575325331228446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360740454610503823, 360740454706677864⟩, ⟨(-723323625414342540), (-723323338685677646)⟩, true⟩

def words08 : List Nat := [360575370783822255, 360575419552829974, 360575442150244137, 360575464737356538, 360575473230378004, 360575521027869006, 360575593149744579, 360575665238764557, 360575688570252500, 360575726093904993]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361255798410775407, 361255798507411364⟩, ⟨(-2988544149748422336), (-2988543860989631396)⟩, true⟩

def words09 : List Nat := [360575814884970435, 360575903635626563, 360576011953488924, 360576104502452238, 360576153665193361, 360576202805577242, 360576303084022112, 360576429591432994, 360576583993499097, 360576738325409630]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk043
