import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk872A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk872B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk872A

def state06 : KState := ⟨⟨362487383653203497, 362487498597058751⟩, ⟨(-208032013309258912), (-201259745995472976)⟩, true⟩

def words05 : List Nat := [371285192754237933, 371285192678848827, 371285192654099736, 371285192657136933, 371285192536736386, 371285192386393780, 371285192234775064, 371285192215653041, 371285192156063135, 371285192185878551]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469402908856809, 362469517880167455⟩, ⟨1361053885537723426, 1367828548745803336⟩, true⟩

def words06 : List Nat := [371285192188157517, 371285192184953951, 371285192094536104, 371285192073366521, 371285192055824699, 371285192058862382, 371285191891380384, 371285191720323326, 371285191548107860, 371285191405419499]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473360508456527, 362473475507135984⟩, ⟨1015698632082384872, 1022475683909388994⟩, true⟩

def words07 : List Nat := [371285191227883601, 371285191178391131, 371285191127867901, 371285191078330988, 371285190910052102, 371285190782307285, 371285190652959967, 371285190655742771, 371285190528875402, 371285190398106532]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483342090827324, 362483457116734996⟩, ⟨144465001773851108, 151244430218091034⟩, true⟩

def words08 : List Nat := [371285190265946340, 371285190266258756, 371285190216052758, 371285190199482531, 371285190182013523, 371285190117401688, 371285189915882696, 371285189839022773, 371285189779703107, 371285189782907732]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483001848725244, 362483116902306529⟩, ⟨174182766422533366, 180964610631518400⟩, true⟩

def words09 : List Nat := [371285189765354160, 371285189740693752, 371285189817995455, 371285189858964317, 371285189906243801, 371285189954739481, 371285189977062164, 371285189980101076, 371285189827328326, 371285189807353855]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk872B
