import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk483A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360530158703386227, 360530173297332291⟩, ⟨2522397309322282263, 2522873626010942459⟩, true⟩

def state01 : KState := ⟨⟨360498845106023006, 360498859706221003⟩, ⟨4034944358674179314, 4035420977363569844⟩, true⟩

def words00 : List Nat := [360582405624864613, 360582404609895942, 360582403166198333, 360582401509737766, 360582399853237237, 360582398090024351, 360582396591215437, 360582394965284445, 360582393339344870, 360582391500411928]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571084520615110, 360571099127086031⟩, ⟨544719623652059969, 545196545417411839⟩, true⟩

def words01 : List Nat := [360582389771906404, 360582388470747536, 360582387169435757, 360582386295370011, 360582385692736261, 360582384722530677, 360582383752238776, 360582382968533884, 360582382400998201, 360582382168174968]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360535154425685700, 360535169038502613⟩, ⟨2280823656104691090, 2281300884538776658⟩, true⟩

def words02 : List Nat := [360582381935284141, 360582381334617009, 360582380493305509, 360582379539249268, 360582378585056990, 360582377518359760, 360582376158070182, 360582374560266380, 360582372962390199, 360582371622498864]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360510193614344238, 360510208233421152⟩, ⟨3487392641418793185, 3487870172430332175⟩, true⟩

def words03 : List Nat := [360582370646385623, 360582369816655487, 360582368986886672, 360582367944225263, 360582367029197006, 360582365816722350, 360582364604101129, 360582363818272973, 360582362604408340, 360582361112453638]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360539830943107497, 360539845568473782⟩, ⟨2054699329874299083, 2055177164944846277⟩, true⟩

def words04 : List Nat := [360582359620409961, 360582358555198230, 360582357817526487, 360582357313332141, 360582356809110752, 360582355892718193, 360582354781581434, 360582353797041127, 360582352812346932, 360582351818007285]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk483A
