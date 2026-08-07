import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk363

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362462314232467005, 362462332782710363⟩, ⟨821368663353135292, 821823740641706656⟩, true⟩

def state01 : KState := ⟨⟨362460025411623564, 362460043972398482⟩, ⟨904550097099843095, 905005556739208013⟩, true⟩

def words00 : List Nat := [371284971940716330, 371284971941918210, 371284971322821418, 371284970702061977, 371284970080870054, 371284969614506721, 371284968767907702, 371284968679697561, 371284968591125287, 371284968388722889]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498254560300303, 362498273131763110⟩, ⟨(-483771732319252093), (-483315884548466419)⟩, true⟩

def words01 : List Nat := [371284967703115446, 371284967399515785, 371284967547962909, 371284967549144894, 371284967116972153, 371284966564522329, 371284966011612975, 371284965998881545, 371284965975007506, 371284966342727884]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481981906910990, 362482000489052750⟩, ⟨107295519903962238, 107751755589184630⟩, true⟩

def words02 : List Nat := [371284966707865370, 371284966709061058, 371284966871724114, 371284967110861138, 371284967573272628, 371284967574455330, 371284967164316213, 371284966752659471, 371284966404433600, 371284966405804448]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362441357134736896, 362441375727505399⟩, ⟨1583543566967254806, 1584000188776823970⟩, true⟩

def words03 : List Nat := [371284966876747873, 371284967429767127, 371284967821253251, 371284967822436541, 371284967346887308, 371284966997792529, 371284966648104678, 371284966460196640, 371284965263289217, 371284964065116209]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476275667877476, 362476294271236669⟩, ⟨314535977200309122, 314992983928756354⟩, true⟩

def words04 : List Nat := [371284962866493197, 371284962424864738, 371284961608924013, 371284961549924298, 371284961490518134, 371284961316406817, 371284960370177986, 371284959980739414, 371284959826652557, 371284959827878451]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490694206374289, 362490712820540637⟩, ⟨(-209663354884899680), (-209205955262758678)⟩, true⟩

def words05 : List Nat := [371284959590401085, 371284959188413157, 371284959138676513, 371284959173102784, 371284959253129946, 371284959333589294, 371284959411998575, 371284959413203089, 371284959079908278, 371284959239636296]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467666730013382, 362467685354718863⟩, ⟨627736683977357879, 628194466857264805⟩, true⟩

def words06 : List Nat := [371284959904519991, 371284959905703493, 371284959563279266, 371284959108011729, 371284958652341781, 371284958236581343, 371284957669361286, 371284957671762065, 371284957678675200, 371284957679900531]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497922666984476, 362497941302393722⟩, ⟨(-472751639145281837), (-472293466915053233)⟩, true⟩

def words07 : List Nat := [371284957309818853, 371284957415247138, 371284958275063215, 371284958412437247, 371284958413354732, 371284958372542286, 371284958669343906, 371284958715055904, 371284959072734152, 371284959430897198]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495837747368847, 362495856393461682⟩, ⟨(-397010769810947805), (-396552208856678129)⟩, true⟩

def words08 : List Nat := [371284959739332342, 371284959740516791, 371284959098636123, 371284959156041998, 371284959379358504, 371284959380565323, 371284959130749357, 371284958871905857, 371284959106899582, 371284959407699910]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362464482188351525, 362464500845144125⟩, ⟨744323577695492851, 744782528067103349⟩, true⟩

def words09 : List Nat := [371284960366496122, 371284961325731342, 371284962140349789, 371284962141535648, 371284962212331603, 371284962314313452, 371284962891404661, 371284962892589732, 371284962464362341, 371284961903607507]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk363
