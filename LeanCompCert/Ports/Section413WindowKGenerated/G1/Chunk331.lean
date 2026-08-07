import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk331

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362463052308231652, 362463067614594402⟩, ⟨714681304903849966, 715023733158214460⟩, true⟩

def state01 : KState := ⟨⟨362493088600525498, 362493103916468619⟩, ⟨(-279682154829418233), (-279339409415840125)⟩, true⟩

def words00 : List Nat := [371284669032246916, 371284669033436664, 371284668800260450, 371284668873214983, 371284668874042714, 371284668794903503, 371284667500227453, 371284667117378026, 371284667207106869, 371284667463041787]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505650020053207, 362505665345756820⟩, ⟨(-695621183955795741), (-695278115324577159)⟩, true⟩

def words01 : List Nat := [371284667719902974, 371284667977107328, 371284669144753417, 371284669857970472, 371284670720358062, 371284671583095571, 371284672288888970, 371284672289960132, 371284672647683921, 371284673282856408]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479038943240358, 362479054278470124⟩, ⟨185867974517210453, 186211358704200945⟩, true⟩

def words02 : List Nat := [371284674385411595, 371284674386481902, 371284674274967809, 371284674117435612, 371284674032762060, 371284674033940882, 371284674072913082, 371284674493475028, 371284674903945569, 371284674905053409]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499610951309723, 362499626296222296⟩, ⟨(-495846794793883575), (-495503089766288755)⟩, true⟩

def words03 : List Nat := [371284674943647908, 371284675152415784, 371284675930167022, 371284675931237706, 371284675495925459, 371284674911043862, 371284674340109615, 371284674341320199, 371284674481820654, 371284674934170268]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362456475088553499, 362456490443116480⟩, ⟨933753241419257751, 934097266310590985⟩, true⟩

def words04 : List Nat := [371284675385678264, 371284675386749256, 371284674777400392, 371284674430825472, 371284674083747325, 371284673773129561, 371284672250068557, 371284670643619794, 371284669036842950, 371284668339536106]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362450630457702992, 362450645821933022⟩, ⟨1127700989604848105, 1128045335007164265⟩, true⟩

def words05 : List Nat := [371284667549156160, 371284667609229737, 371284667627435667, 371284667628514039, 371284666870118531, 371284666297937545, 371284665947304136, 371284665948375559, 371284665101609892, 371284664076909113]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481714973795597, 362481730347613266⟩, ⟨96866970549513961, 97211633927657127⟩, true⟩

def words06 : List Nat := [371284663051785157, 371284662935597870, 371284662394602431, 371284662424834550, 371284662425677261, 371284662147068924, 371284661278021582, 371284660978790328, 371284661055997626, 371284661057107619]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486956976934945, 362486972360520557⟩, ⟨(-77037512573926427), (-76692525144692395)⟩, true⟩

def words07 : List Nat := [371284660969557615, 371284660881672635, 371284661087057447, 371284661088251336, 371284661265995532, 371284661492063943, 371284661717129512, 371284661718201619, 371284660950951337, 371284661021948944]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362456128486885763, 362456143880013393⟩, ⟨946146510503481636, 946491814586812066⟩, true⟩

def words08 : List Nat := [371284661999535664, 371284662000608133, 371284661946877475, 371284661889218501, 371284662049571056, 371284662050751930, 371284661816925236, 371284661678788856, 371284661540314540, 371284661259181420]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362524112191882650, 362524127594713495⟩, ⟨(-1310573781174953941), (-1310228154993277447)⟩, true⟩

def words09 : List Nat := [371284660448347724, 371284660497276724, 371284661215671722, 371284661216762777, 371284661183828909, 371284661001860931, 371284661416951043, 371284661700569531, 371284662890029568, 371284664079909927]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk331
