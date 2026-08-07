import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk143

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490995528651541, 362490998186288680⟩, ⟨(-98906844808248022), (-98881134353665234)⟩, true⟩

def state01 : KState := ⟨⟨362429506869297152, 362429509530826552⟩, ⟨780439790914765089, 780465557048396467⟩, true⟩

def words00 : List Nat := [371284083905495530, 371284083187860699, 371284075974328637, 371284073628210256, 371284071282202340, 371284070468090860, 371284064473263031, 371284058267204015, 371284052061834101, 371284049402038879]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362353334627100041, 362353337292509464⟩, ⟨1871106971472427307, 1871132793149325287⟩, true⟩

def words01 : List Nat := [371284045591288300, 371284044265715439, 371284042940180945, 371284041492062848, 371284035130299797, 371284028919260225, 371284022708871186, 371284020652491171, 371284012115202563, 371284002990355088]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362466174544092049, 362466177213370464⟩, ⟨255108023162895192, 255133900263319278⟩, true⟩

def words02 : List Nat := [371283993866585783, 371283989598253735, 371283984195172424, 371283983646575716, 371283983097926158, 371283981905529850, 371283978701769216, 371283979526003921, 371283981392984086, 371283981393430710]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362433477534776044, 362433480207983137⟩, ⟨723884726581223242, 723910659999675838⟩, true⟩

def words03 : List Nat := [371283980151400397, 371283978328352235, 371283977160472385, 371283977160947757, 371283975394431799, 371283974515623736, 371283973636782632, 371283972403054226, 371283965642979492, 371283962122906406]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362430200417154951, 362430203094216882⟩, ⟨770937216943736792, 770963205660588656⟩, true⟩

def words04 : List Nat := [371283959927316619, 371283959927748865, 371283955599029865, 371283950410448100, 371283945222418961, 371283940955110633, 371283934276230906, 371283932440346807, 371283930604576086, 371283928753147934]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489626973441999, 362489629654414144⟩, ⟨(-82061306486715802), (-82035261638775824)⟩, true⟩

def words05 : List Nat := [371283925507984298, 371283926006669901, 371283930541878798, 371283930542311224, 371283928626395549, 371283925171025207, 371283921715970009, 371283920311490461, 371283916891972412, 371283917290258530]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463325334081455, 362463328018960205⟩, ⟨295513529845282102, 295539630811736108⟩, true⟩

def words06 : List Nat := [371283917673682121, 371283917674114926, 371283912624287337, 371283911597125811, 371283910569886703, 371283909834730540, 371283904791190791, 371283899735756019, 371283894680843990, 371283894451167007]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362405743990683851, 362405746679459316⟩, ⟨1123309249720460894, 1123335406703203140⟩, true⟩

def words07 : List Nat := [371283893558290798, 371283894096612540, 371283894641288166, 371283894641721174, 371283888755194489, 371283883492443429, 371283878230199943, 371283875435190539, 371283870012081297, 371283864579786382]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477827856671910, 362477830549325410⟩, ⟨86558905874096821, 86585118642581637⟩, true⟩

def words08 : List Nat := [371283859148059526, 371283858038736383, 371283855966374807, 371283856688912236, 371283856689253585, 371283856155801935, 371283849203758148, 371283847060940695, 371283847582833902, 371283847583282504]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362434778271835128, 362434780968454291⟩, ⟨706543869697185324, 706570139550930592⟩, true⟩

def words09 : List Nat := [371283847165501090, 371283846370541281, 371283848458141033, 371283848934782145, 371283850918974221, 371283852903052294, 371283854878765682, 371283854879200119, 371283851746401218, 371283848339256439]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk143
