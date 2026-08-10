import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk407A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk407B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk407A

def state06 : KState := ⟨⟨360588494889072404, 360588505138186504⟩, ⟨(-245433554506855252), (-245151214294923088)⟩, true⟩

def words05 : List Nat := [360582498140522565, 360582496816933070, 360582495493241150, 360582494628283188, 360582494015592101, 360582492853212712, 360582491690783960, 360582490937652493, 360582490632847185, 360582490780975079]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598949611834456, 360598959866230420⟩, ⟨(-671850234839097694), (-671567679313314742)⟩, true⟩

def words06 : List Nat := [360582490781481090, 360582490467339727, 360582489740323656, 360582489613772976, 360582489487082338, 360582489096563230, 360582488919429910, 360582488400179533, 360582487880836626, 360582488166264432]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560399570788961, 360560409830390769⟩, ⟨900235416816568705, 900518184611137061⟩, true⟩

def words07 : List Nat := [360582489170785368, 360582490175362854, 360582490878290689, 360582491689755038, 360582492069470947, 360582492449306040, 360582492883835409, 360582492884388835, 360582492720144196, 360582492179204186]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579849695915969, 360579859960749285⟩, ⟨107011401894647473, 107294383056261421⟩, true⟩

def words08 : List Nat := [360582491638167699, 360582491374443880, 360582491681262485, 360582491988170725, 360582491988681068, 360582491787012465, 360582490986584751, 360582490785945973, 360582490585153010, 360582490369747968]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360546993559173856, 360547003829279037⟩, ⟨1447443585337072389, 1447726781564171443⟩, true⟩

def words09 : List Nat := [360582490305756141, 360582489940670461, 360582489575497804, 360582489635506742, 360582489635970356, 360582489578444923, 360582489520856829, 360582489158606184, 360582488197908599, 360582487328827179]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk407B
