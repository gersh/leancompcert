import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk438

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480644930659677, 362480672354727144⟩, ⟨211736141392449597, 212547735891438651⟩, true⟩

def state01 : KState := ⟨⟨362488707330350755, 362488734767304948⟩, ⟨(-141374033965950021), (-140561874962318857)⟩, true⟩

def words00 : List Nat := [371285525343568200, 371285525345024534, 371285525307797452, 371285525265651104, 371285525336077966, 371285525337699461, 371285525636665338, 371285526012055219, 371285526323094137, 371285526397832389]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362507627662751058, 362507655112777015⟩, ⟨(-970383972711981965), (-969571240967457373)⟩, true⟩

def words01 : List Nat := [371285526932073056, 371285527467037788, 371285528048615891, 371285528093946330, 371285528095067864, 371285528008218649, 371285528258520727, 371285528378805803, 371285528884734934, 371285529391297189]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482703647877250, 362482731110969189⟩, ⟨121838187130476241, 122651491492435539⟩, true⟩

def words02 : List Nat := [371285529886379910, 371285529887827271, 371285529829094438, 371285529971165094, 371285530273840536, 371285530275291869, 371285530048736186, 371285529719241895, 371285529454991282, 371285529456656902]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480385047677726, 362480412523814811⟩, ⟨223570408504624804, 224384284702381404⟩, true⟩

def words03 : List Nat := [371285529770744335, 371285530149258925, 371285530512242068, 371285530514937933, 371285530536821038, 371285530559402977, 371285531005061119, 371285531006511148, 371285530893588218, 371285530778484118]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487578029225312, 362487605518346341⟩, ⟨(-91780297428961572), (-90965851951359822)⟩, true⟩

def words04 : List Nat := [371285530761652702, 371285530763247754, 371285530769806454, 371285530936988743, 371285530990918646, 371285530992376642, 371285530619732805, 371285530659639258, 371285531039035924, 371285531087844155]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483784695892507, 362483812198177388⟩, ⟨74629019989938551, 75444042769280805⟩, true⟩

def words05 : List Nat := [371285531116632803, 371285531145898392, 371285531694571995, 371285531984992317, 371285532294414164, 371285532604376539, 371285532820938993, 371285532822387540, 371285532346028653, 371285532308591645]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488054739943516, 362488082255146936⟩, ⟨(-112608193646315636), (-111792604191833672)⟩, true⟩

def words06 : List Nat := [371285532602044146, 371285532632728146, 371285532661924850, 371285532691621594, 371285532864894172, 371285532866505129, 371285533215982028, 371285533651589402, 371285533983662433, 371285534043248602]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501907150636134, 362501934678953383⟩, ⟨(-720339557188508452), (-719523392364566050)⟩, true⟩

def words07 : List Nat := [371285534482067247, 371285534921634238, 371285535815877204, 371285536018290186, 371285536172283822, 371285536326716862, 371285536669191721, 371285536777729281, 371285537152418334, 371285537527740682]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480072016853628, 362480099558274582⟩, ⟨237785257052883615, 238601996931813963⟩, true⟩

def words08 : List Nat := [371285537901516241, 371285537902966643, 371285537679767900, 371285537672933805, 371285537765510608, 371285537766960367, 371285537176304954, 371285536585291536, 371285535993689884, 371285535921841040]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469977616944118, 362470005171380619⟩, ⟨681004911110183249, 681822222309284485⟩, true⟩

def words09 : List Nat := [371285536194091848, 371285536590761200, 371285536983999070, 371285536985453432, 371285536871710582, 371285536894321530, 371285537131866073, 371285537133317102, 371285536781470167, 371285536429291993]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk438
