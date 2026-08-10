import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk828A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk828B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk828A

def state06 : KState := ⟨⟨362485126329722499, 362485229561508498⟩, ⟨(-374022234587240), 5401775869545472⟩, true⟩

def words05 : List Nat := [371285294099097383, 371285294154402303, 371285294318557780, 371285294411280557, 371285294534781816, 371285294659405825, 371285294777833410, 371285294780713590, 371285294750367623, 371285294753107214]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479826257871704, 362479929515238677⟩, ⟨438824730076526068, 444602647955284142⟩, true⟩

def words06 : List Nat := [371285294827381409, 371285294830267700, 371285294765953028, 371285294681849047, 371285294596608903, 371285294557105270, 371285294501677871, 371285294543473121, 371285294573782085, 371285294576756178]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500114128409641, 362500217411831630⟩, ⟨(-1242541838405504843), (-1236761761220642073)⟩, true⟩

def words07 : List Nat := [371285294580303196, 371285294650136315, 371285294778349996, 371285294781242474, 371285294779420252, 371285294758893360, 371285294848643655, 371285294907956387, 371285295089954811, 371285295273329192]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489788356947825, 362489891666280019⟩, ⟨(-386720332783676462), (-380938108025370640)⟩, true⟩

def words08 : List Nat := [371285295455515960, 371285295479994954, 371285295649179796, 371285295819819415, 371285295989343296, 371285295992216628, 371285295967855961, 371285295916991639, 371285295956513462, 371285296015268144]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488728977087353, 362488832312270150⟩, ⟨(-298833974448595414), (-293049606803759892)⟩, true⟩

def words09 : List Nat := [371285296218270710, 371285296422425724, 371285296625310455, 371285296728806857, 371285296859173314, 371285296991020419, 371285297228643221, 371285297287090893, 371285297331901865, 371285297377748206]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk828B
