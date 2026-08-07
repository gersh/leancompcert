import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk369

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

def state06 : KState := ⟨⟨360567637561350285, 360567645921669371⟩, ⟨515331972372325021, 515540851070673925⟩, true⟩

def words05 : List Nat := [360581595034268717, 360581595132776756, 360581595208574319, 360581595658115731, 360581595761326456, 360581595864612018, 360581595865055351, 360581595507697480, 360581594914596807, 360581594537769769]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360538863390992775, 360538871755989457⟩, ⟨1578907654684436805, 1579116706291012963⟩, true⟩

def words06 : List Nat := [360581594160785404, 360581594122553448, 360581593353613946, 360581592118241941, 360581590882855534, 360581589460253488, 360581588508672008, 360581587534949485, 360581586561225214, 360581585218426326]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613778335878950, 360613786705575253⟩, ⟨(-1191181377662739706), (-1190972152288214028)⟩, true⟩

def words07 : List Nat := [360581584063508143, 360581583014652144, 360581581965699428, 360581581647904576, 360581581602775540, 360581580839249468, 360581580075669385, 360581579988621319, 360581580859946486, 360581581731337450]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597234214772820, 360597242589221423⟩, ⟨(-579477796348057741), (-579268395210520591)⟩, true⟩

def words08 : List Nat := [360581582021737509, 360581582399296935, 360581583209448535, 360581584019702755, 360581584414518034, 360581584415016089, 360581584080045963, 360581583376516387, 360581582672921077, 360581582877529106]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360561344323983991, 360561352703121512⟩, ⟨748299615058295951, 748509189662302005⟩, true⟩

def words09 : List Nat := [360581583806980599, 360581584736478516, 360581585014388997, 360581585014887339, 360581584829235921, 360581584112764772, 360581583409191957, 360581583409692516, 360581583227474976, 360581582681220494]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk369
