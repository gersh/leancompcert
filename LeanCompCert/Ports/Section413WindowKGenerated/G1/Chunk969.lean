import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk969

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486058164233133, 362486201059568222⟩, ⟨(-94405960260561627), (-85057385303901273)⟩, true⟩

def state01 : KState := ⟨⟨362482739108166963, 362482882033798790⟩, ⟨227209418081891782, 236560928952024130⟩, true⟩

def words00 : List Nat := [371285323330782499, 371285323334198321, 371285323280191524, 371285323209218548, 371285323136913346, 371285323097932285, 371285323027668060, 371285323048424777, 371285323067598475, 371285323071142223]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499613110901246, 362499756067271983⟩, ⟨(-1408118773620898094), (-1398764283687365992)⟩, true⟩

def words01 : List Nat := [371285323129697157, 371285323215288129, 371285323401788683, 371285323467316186, 371285323517187893, 371285323568028395, 371285323684577989, 371285323759046293, 371285323910266080, 371285324063024324]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489967900556132, 362490110887671531⟩, ⟨(-473253700116227825), (-463896230256505721)⟩, true⟩

def words02 : List Nat := [371285324193271321, 371285324259051846, 371285324417097793, 371285324576869976, 371285324767747861, 371285324817695026, 371285324866393616, 371285324916306849, 371285324994653777, 371285325047947847]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488110343523627, 362488253361213887⟩, ⟨(-293143715593503416), (-283783281955401764)⟩, true⟩

def words03 : List Nat := [371285325206202764, 371285325365833842, 371285325523926114, 371285325573900708, 371285325654794623, 371285325737472293, 371285325879787737, 371285325913043610, 371285325945807436, 371285325979796784]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487298746548281, 362487441794713341⟩, ⟨(-214466683294104291), (-205103295272030173)⟩, true⟩

def words04 : List Nat := [371285326082164765, 371285326136543460, 371285326201830373, 371285326268490682, 371285326309744357, 371285326313145718, 371285326212190528, 371285326191429367, 371285326233671101, 371285326259079134]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491802222750618, 362491945301929394⟩, ⟨(-651086539488828817), (-641720144534541067)⟩, true⟩

def words05 : List Nat := [371285326270890439, 371285326283874805, 371285326401970933, 371285326498835792, 371285326626236638, 371285326754908287, 371285326861118479, 371285326864520299, 371285326896830886, 371285326969357179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480261991368156, 362480405100837275⟩, ⟨467926789597407753, 477296121660865777⟩, true⟩

def words06 : List Nat := [371285327128956286, 371285327147814362, 371285327165420406, 371285327184209233, 371285327187192986, 371285327190977529, 371285327157868651, 371285327178817687, 371285327198188183, 371285327201710338]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493897680143532, 362494040820377509⟩, ⟨(-854419397278999856), (-845047081791977496)⟩, true⟩

def words07 : List Nat := [371285327153299496, 371285327149807604, 371285327243536989, 371285327246939245, 371285327206752698, 371285327150546636, 371285327114998125, 371285327118813229, 371285327194359731, 371285327288017645]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481819188756399, 362481962359641525⟩, ⟨316974362002337242, 326349650194194048⟩, true⟩

def words08 : List Nat := [371285327380036778, 371285327383439361, 371285327380665940, 371285327432025328, 371285327464066387, 371285327467469610, 371285327371925109, 371285327258149325, 371285327143020637, 371285327135909122]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476912417707795, 362477055619308602⟩, ⟨792933705272846634, 802311972733328328⟩, true⟩

def words09 : List Nat := [371285327145096972, 371285327190471921, 371285327232784454, 371285327236187651, 371285327136580519, 371285327063493497, 371285327017977807, 371285327021404427, 371285326958170617, 371285326876759462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk969
