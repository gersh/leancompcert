import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk731A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk731B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk731A

def state06 : KState := ⟨⟨362502053603287643, 362502133310662583⟩, ⟨(-1234993214116154970), (-1231055094640227234)⟩, true⟩

def words05 : List Nat := [371285305215848606, 371285305376426344, 371285305707955845, 371285305815858644, 371285305892315444, 371285305969530132, 371285306121709612, 371285306188534093, 371285306420243099, 371285306653090377]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483995336812993, 362484075066897284⟩, ⟨86192682662519774, 90132463668349096⟩, true⟩

def words06 : List Nat := [371285306849979013, 371285306852492461, 371285306912673476, 371285307011366864, 371285307165527508, 371285307168041147, 371285307073426191, 371285306966546176, 371285306886655622, 371285306889552312]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472675218216506, 362472754970917367⟩, ⟨914564206690756458, 918505642670904888⟩, true⟩

def words07 : List Nat := [371285306935721641, 371285306999713067, 371285307063351189, 371285307065864975, 371285306880565622, 371285306754504603, 371285306627129597, 371285306621732569, 371285306460248143, 371285306291533259]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488723053125292, 362488802828329032⟩, ⟨(-259886659515448000), (-255943576661472294)⟩, true⟩

def words08 : List Nat := [371285306136766218, 371285306139536369, 371285306080457203, 371285306100911125, 371285306102896598, 371285306040852307, 371285305821214934, 371285305770428971, 371285305851036046, 371285305901430077]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487366916349316, 362487446714506904⟩, ⟨(-160575357784065493), (-156630594823375657)⟩, true⟩

def words09 : List Nat := [371285305952513300, 371285306004513465, 371285306213933184, 371285306359419402, 371285306560605222, 371285306762728692, 371285306964469037, 371285306966983848, 371285306949128092, 371285306981513866]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk731B
