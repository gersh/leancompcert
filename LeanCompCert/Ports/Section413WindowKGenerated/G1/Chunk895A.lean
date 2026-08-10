import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk895A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478455374484258, 362478576532031252⟩, ⟨580349030681485807, 587670496095195591⟩, true⟩

def state01 : KState := ⟨⟨362474289300171209, 362474410485692907⟩, ⟨953302353710109117, 960626323003934581⟩, true⟩

def words00 : List Nat := [371285142662941005, 371285142671939900, 371285142733842280, 371285142797056076, 371285142842531614, 371285142845653481, 371285142724477262, 371285142652376845, 371285142578734161, 371285142541586148]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487182975791294, 362487304189791321⟩, ⟨(-200884372386180812), (-193557853853672380)⟩, true⟩

def words01 : List Nat := [371285142424023068, 371285142307392959, 371285142194122579, 371285142197595734, 371285142141752093, 371285142125167559, 371285142107493853, 371285142085722420, 371285142011461463, 371285142039526538]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486577826404458, 362486699068233431⟩, ⟨(-146691296208488259), (-139362286284203733)⟩, true⟩

def words02 : List Nat := [371285142190475544, 371285142214874617, 371285142217274323, 371285142209371217, 371285142226634088, 371285142230076754, 371285142295627709, 371285142393102599, 371285142466191949, 371285142486867377]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490482704102088, 362490603974122077⟩, ⟨(-496295943765515975), (-488964409756908705)⟩, true⟩

def words03 : List Nat := [371285142564618382, 371285142643981476, 371285142846373753, 371285142898136025, 371285142927518053, 371285142957916208, 371285143038720652, 371285143058609969, 371285143121725188, 371285143186217577]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480537847619571, 362480659145825356⟩, ⟨394179548731938713, 401513606635917299⟩, true⟩

def words04 : List Nat := [371285143250163303, 371285143253286540, 371285143155360260, 371285143163781593, 371285143208552606, 371285143211675919, 371285143090408728, 371285142966587691, 371285142841525408, 371285142826524808]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk895A
