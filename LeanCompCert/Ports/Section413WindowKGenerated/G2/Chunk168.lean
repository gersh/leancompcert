import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk168

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596373001467434, 360596374613924381⟩, ⟨(-226360356435357128), (-226342017920791930)⟩, true⟩

def state01 : KState := ⟨⟨360574060466246021, 360574062080698721⟩, ⟨148591028649504463, 148609400703016423⟩, true⟩

def words00 : List Nat := [360582905778406987, 360582906965269178, 360582906965459852, 360582906354231637, 360582905743041644, 360582904436660282, 360582904588094197, 360582904739549013, 360582904739738902, 360582902616136141]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360637878700821587, 360637880317277325⟩, ⟨(-924486258633933995), (-924467852899345213)⟩, true⟩

def words01 : List Nat := [360582905088082910, 360582908085614960, 360582910115847978, 360582912277938984, 360582912278135078, 360582911290257275, 360582911591761184, 360582914632069565, 360582917900119275, 360582921167827272]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360669298734983248, 360669300353466771⟩, ⟨(-1453696811313591636), (-1453678371462218784)⟩, true⟩

def words02 : List Nat := [360582921636455000, 360582921636668415, 360582924128450396, 360582927133451524, 360582929227047945, 360582929227260477, 360582929198132851, 360582926999126573, 360582926118433717, 360582931250533956]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360569306608635875, 360569308229118928⟩, ⟨230029389813473440, 230047863327117232⟩, true⟩

def words03 : List Nat := [360582939898329786, 360582948545138673, 360582955225370974, 360582960464762846, 360582962436197011, 360582964407449413, 360582968868294653, 360582969839452229, 360582969839643430, 360582969028603912]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588831032065332, 360588832654559706⟩, ⟨(-98548886697409397), (-98530379303057741)⟩, true⟩

def words04 : List Nat := [360582968217614023, 360582970332120465, 360582976273770387, 360582982214755430, 360582985186552904, 360582985186765713, 360582985273482923, 360582985876214748, 360582985876390122, 360582985501316394]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360530535222510737, 360530536847030762⟩, ⟨884085916585645613, 884104458122479979⟩, true⟩

def words05 : List Nat := [360582985501506151, 360582983547783264, 360582981594250664, 360582982626569135, 360582983213122148, 360582983799643936, 360582983799835388, 360582982613445533, 360582977944013735, 360582974833870767]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360500442488195589, 360500444114725128⟩, ⟨1391180521990713832, 1391199097418136332⟩, true⟩

def words06 : List Nat := [360582971724027582, 360582969612901196, 360582964019682168, 360582955165986896, 360582946313306279, 360582936551083304, 360582928601841075, 360582922982729511, 360582917364260975, 360582909977049855]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360673685833014572, 360673687461556075⟩, ⟨(-1532319729586523827), (-1532301120207427987)⟩, true⟩

def words07 : List Nat := [360582905089197919, 360582903699455140, 360582903148140680, 360582905637246061, 360582905637444762, 360582905142563885, 360582904647703997, 360582905950397450, 360582911328621719, 360582916706256779]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360639704162557156, 360639705793130202⟩, ⟨(-959025071709419587), (-959006428027687617)⟩, true⟩

def words08 : List Nat := [360582919569306788, 360582920959516166, 360582925842372584, 360582930724718819, 360582933255897739, 360582933256111179, 360582932312635180, 360582929128680561, 360582926253039548, 360582929614808748]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360535586174020702, 360535587806608197⟩, ⟨799810767153150605, 799829444868970639⟩, true⟩

def words09 : List Nat := [360582931569748680, 360582933524494685, 360582933717498709, 360582933717712275, 360582930438256464, 360582925664679350, 360582920891603702, 360582918421505882, 360582917793063746, 360582914992695119]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk168
