import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk991

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360560284652126273, 360560349690228459⟩, ⟨2183629110419243869, 2187981135355298911⟩, true⟩

def state01 : KState := ⟨⟨360595547802410555, 360595612854105514⟩, ⟨(-1311145555987827353), (-1306792183940922989)⟩, true⟩

def words00 : List Nat := [360582427986620353, 360582427848914767, 360582427779543857, 360582427796595667, 360582427797923992, 360582427728598536, 360582427661106810, 360582427601452432, 360582427581850562, 360582427716391831]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585999261754082, 360586064327172740⟩, ⟨(-364758957546860298), (-360404225274781806)⟩, true⟩

def words01 : List Nat := [360582427799719316, 360582427883209402, 360582427964013913, 360582428096030280, 360582428184947884, 360582428274098594, 360582428311853293, 360582428313293919, 360582428286100798, 360582428324456114]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569055148860127, 360569120227843356⟩, ⟨1314796570016329562, 1319152646876324038⟩, true⟩

def words02 : List Nat := [360582428377998807, 360582428379440751, 360582428377700771, 360582428297721157, 360582428217515521, 360582428074877395, 360582427983060010, 360582427849927582, 360582427716640575, 360582427527821933]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611226473262247, 360611291565839988⟩, ⟨(-2865878123672043826), (-2861520699121517748)⟩, true⟩

def words03 : List Nat := [360582427394746960, 360582427363807781, 360582427401595738, 360582427503346754, 360582427517852909, 360582427532458461, 360582427648478305, 360582427839531797, 360582428131837447, 360582428424464357]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602724506429171, 360602789612746272⟩, ⟨(-2023057838718121012), (-2018699051980719192)⟩, true⟩

def words04 : List Nat := [360582428638476024, 360582428808586928, 360582428994117904, 360582429180081492, 360582429325836597, 360582429397315377, 360582429417681880, 360582429438230621, 360582429560147394, 360582429767137245]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360584040976833789, 360584106096710862⟩, ⟨(-170488226978218634), (-166128095700636544)⟩, true⟩

def words05 : List Nat := [360582429965890902, 360582430164910301, 360582430299901583, 360582430419477769, 360582430469693823, 360582430520270108, 360582430653836612, 360582430723108321, 360582430741287756, 360582430759676135]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589376055207704, 360589441188712609⟩, ⟨(-699530183442476545), (-695168700762795223)⟩, true⟩

def words06 : List Nat := [360582430765117986, 360582430849720817, 360582431004509866, 360582431159578803, 360582431212772201, 360582431214213657, 360582431236821340, 360582431289803436, 360582431318300126, 360582431390477613]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590442014338695, 360590507161589815⟩, ⟨(-805233663009278004), (-800870817051968024)⟩, true⟩

def words07 : List Nat := [360582431411344138, 360582431432354443, 360582431554708846, 360582431728204397, 360582431875629532, 360582432023323299, 360582432106425701, 360582432154805867, 360582432237389436, 360582432320470529]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588808328843729, 360588873489683450⟩, ⟨(-643216920007975100), (-638852726266498372)⟩, true⟩

def words08 : List Nat := [360582432504658057, 360582432613601900, 360582432644102260, 360582432674737084, 360582432675943578, 360582432722025879, 360582432764560007, 360582432807361705, 360582432808658205, 360582432857708105]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592035365492384, 360592100539937279⟩, ⟨(-963292316780422127), (-958926773474869695)⟩, true⟩

def words09 : List Nat := [360582433025398783, 360582433193509716, 360582433447099812, 360582433599641228, 360582433654558545, 360582433709583454, 360582433734445153, 360582433839286115, 360582433937902420, 360582434036842806]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk991
