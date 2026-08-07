import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk508

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551689471497219, 360551705681816080⟩, ⟨1539400292345477108, 1539956718678691930⟩, true⟩

def state01 : KState := ⟨⟨360584444157581108, 360584460374526532⟩, ⟨(-124625522136942414), (-124068759141635346)⟩, true⟩

def words00 : List Nat := [360582019194296893, 360582018819236252, 360582018745186043, 360582018851962014, 360582018852615504, 360582018634335701, 360582018584418071, 360582018606128196, 360582018606700304, 360582018604847887]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360551953446443491, 360551969670087327⟩, ⟨1526365335453111491, 1526922438826827131⟩, true⟩

def words01 : List Nat := [360582018605473539, 360582018460655095, 360582018315719572, 360582017967421233, 360582017818356309, 360582017572727893, 360582017327035491, 360582016836516148, 360582015959804761, 360582015369395215]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360546854295985811, 360546870526237991⟩, ⟨1785475866067931553, 1786033305310131295⟩, true⟩

def words02 : List Nat := [360582014778756814, 360582014574511420, 360582013984156549, 360582013198365531, 360582012412492885, 360582011432666829, 360582010676474305, 360582009819369306, 360582008962221323, 360582007911744781]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596735052435819, 360596751289313811⟩, ⟨(-750300745560494822), (-749742969494898570)⟩, true⟩

def words03 : List Nat := [360582007221057669, 360582006589536286, 360582005957826695, 360582005712344430, 360582005477118735, 360582004909860318, 360582004342490116, 360582003985870688, 360582004180609769, 360582004471401204]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581599413873487, 360581615657460178⟩, ⟨19099511879816137, 19657629047711797⟩, true⟩

def words04 : List Nat := [360582004472044454, 360582004458603427, 360582004431401949, 360582004475445466, 360582004476033575, 360582004423511210, 360582003985234590, 360582003274261391, 360582002563169488, 360582002238169081]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360550624344653235, 360550640594853220⟩, ⟨1594389394214000629, 1594947847701914123⟩, true⟩

def words05 : List Nat := [360582002532003072, 360582002833562004, 360582002834193324, 360582002791679700, 360582002500083786, 360582001939556876, 360582001378842362, 360582001203986706, 360582000783034212, 360582000167163522]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577468306241656, 360577484563089383⟩, ⟨229086385753154200, 229645177377814852⟩, true⟩

def words06 : List Nat := [360581999551157913, 360581999253155371, 360581999420902997, 360581999588962198, 360581999589610442, 360581999426186584, 360581999081539005, 360581999102492673, 360581999103073974, 360581998916880966]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567212868237779, 360567229131774779⟩, ⟨750855935076308665, 751415067017848275⟩, true⟩

def words07 : List Nat := [360581998828766614, 360581998516210304, 360581998275777775, 360581998579799111, 360581998580392579, 360581998578766231, 360581998577055794, 360581998380722221, 360581997799127035, 360581997509664281]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583102512151967, 360583118782323290⟩, ⟨(-57790741464129888), (-57231271935207664)⟩, true⟩

def words08 : List Nat := [360581997219981425, 360581996883616581, 360581996627108100, 360581996074450859, 360581995521700662, 360581994872753138, 360581994525045715, 360581994472733936, 360581994420347458, 360581994196995134]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598551185685574, 360598567462493170⟩, ⟨(-844010488528750707), (-843450681247073637)⟩, true⟩

def words09 : List Nat := [360581994604854542, 360581995012904106, 360581995805909583, 360581996214046960, 360581996291518927, 360581996369032476, 360581996369614973, 360581996395333806, 360581996721464651, 360581997047742044]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk508
