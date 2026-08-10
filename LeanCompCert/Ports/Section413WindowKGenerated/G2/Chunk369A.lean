import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk369A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575865782275240, 360575874114361948⟩, ⟨212651325033736910, 212859161108764238⟩, true⟩

def state01 : KState := ⟨⟨360542673016620739, 360542681353382917⟩, ⟨1437649843786135777, 1437857852410204099⟩, true⟩

def words00 : List Nat := [360581643076703017, 360581643077199895, 360581642921944969, 360581642396555952, 360581641871108591, 360581640805630170, 360581640108974997, 360581639242895228, 360581638376812531, 360581637133724565]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562484793223886, 360562493134684244⟩, ⟨706155183537518221, 706363365594488219⟩, true⟩

def words01 : List Nat := [360581636078735712, 360581635001528291, 360581633924233718, 360581633580254650, 360581632503799962, 360581630741695816, 360581628979589923, 360581627172095171, 360581625921230753, 360581625403524832]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360542206929903755, 360542215276092546⟩, ⟨1454660248878884221, 1454868605533451027⟩, true⟩

def words02 : List Nat := [360581624885773194, 360581623953413726, 360581622288791474, 360581621357291948, 360581620425717535, 360581618976091330, 360581617123071394, 360581614697986719, 360581612272938198, 360581610580872765]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360528586598573700, 360528594949452645⟩, ⟨1957807084622092129, 1958015614507426823⟩, true⟩

def words03 : List Nat := [360581609514547526, 360581609181031269, 360581608847472227, 360581608046717841, 360581606788110269, 360581605225775439, 360581603663372985, 360581602556070255, 360581601679344960, 360581600244918466]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598989752420403, 360598998107993350⟩, ⟨(-643273318646204286), (-643064615341228260)⟩, true⟩

def words04 : List Nat := [360581598810458445, 360581597265637239, 360581596163432197, 360581595793676465, 360581595423906000, 360581594419741024, 360581594022940939, 360581594190981681, 360581594464302207, 360581594935810156]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk369A
