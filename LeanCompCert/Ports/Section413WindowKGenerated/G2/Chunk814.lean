import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk814

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579838444143767, 360579881660101865⟩, ⟨188000873331148654, 190376653178529676⟩, true⟩

def state01 : KState := ⟨⟨360615163794606079, 360615207021572864⟩, ⟨(-2687712851165594026), (-2685336175156827550)⟩, true⟩

def words00 : List Nat := [360582220533862137, 360582220732787866, 360582220882109898, 360582221031634731, 360582221046439935, 360582221078902241, 360582221230479538, 360582221382395684, 360582221684696446, 360582222091094713]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592229740560206, 360592272978625929⟩, ⟨(-820519273132271433), (-818141693503582629)⟩, true⟩

def words01 : List Nat := [360582222383632592, 360582222676283497, 360582223019621839, 360582223438928328, 360582223784948435, 360582224131148186, 360582224361302011, 360582224441072331, 360582224565435448, 360582224690180644]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611717626517849, 360611760875555297⟩, ⟨(-2407330282331230484), (-2404951809329289692)⟩, true⟩

def words02 : List Nat := [360582224965224348, 360582225217526175, 360582225389115282, 360582225560837799, 360582225692816262, 360582225922363725, 360582226272142671, 360582226622136437, 360582226896580861, 360582227260478370]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360619480327833099, 360619523587896924⟩, ⟨(-3039569479887929175), (-3037190108954622297)⟩, true⟩

def words03 : List Nat := [360582227620237978, 360582227980335247, 360582228361078764, 360582228676023091, 360582228855652171, 360582229035367299, 360582229227474352, 360582229536102908, 360582229994978517, 360582230454107376]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602397562569990, 360602440833747770⟩, ⟨(-1648362525645182235), (-1645982249537820391)⟩, true⟩

def words04 : List Nat := [360582230837288850, 360582231126292252, 360582231485717517, 360582231845483740, 360582232077943574, 360582232192079874, 360582232201284819, 360582232210613988, 360582232333329662, 360582232582780467]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360585205692786002, 360585248974961619⟩, ⟨(-247968440154571699), (-245587268217575111)⟩, true⟩

def words05 : List Nat := [360582232935581525, 360582233288617465, 360582233547790736, 360582233687294737, 360582233727681772, 360582233768370492, 360582233959267435, 360582234115294586, 360582234153373232, 360582234191590220]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625960204255048, 360626003497439254⟩, ⟨(-3568056263113052441), (-3565674194362393739)⟩, true⟩

def words06 : List Nat := [360582234277317015, 360582234438897708, 360582234750665178, 360582235062651704, 360582235245868529, 360582235532528142, 360582235907310191, 360582236282438348, 360582236782172812, 360582237320586603]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607199100466810, 360607242404776600⟩, ⟨(-2039501369311095166), (-2037118394104853574)⟩, true⟩

def words07 : List Nat := [360582237763396364, 360582238206320269, 360582238619441413, 360582239132201551, 360582239605252715, 360582240078481453, 360582240435605208, 360582240642588571, 360582240950377405, 360582241258569450]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593208281141466, 360593251596437914⟩, ⟨(-899487453100752254), (-897103582647201264)⟩, true⟩

def words08 : List Nat := [360582241617194154, 360582241861692489, 360582242019857451, 360582242178151340, 360582242270499153, 360582242439727210, 360582242604599505, 360582242769682482, 360582242838539033, 360582242974839858]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609395783553177, 360609439109864346⟩, ⟨(-2218674808788726832), (-2216290040691452446)⟩, true⟩

def words09 : List Nat := [360582243177904418, 360582243381304587, 360582243704851567, 360582244032365143, 360582244232078945, 360582244431868706, 360582244676212860, 360582245031203763, 360582245365824090, 360582245700695239]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk814
