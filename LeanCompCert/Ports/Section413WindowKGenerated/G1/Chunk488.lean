import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk488

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490278086082309, 362490312429419921⟩, ⟨(-258245396973259207), (-257113102444284333)⟩, true⟩

def state01 : KState := ⟨⟨362476206377998553, 362476240735994569⟩, ⟨428477600765365739, 429610610699895583⟩, true⟩

def words00 : List Nat := [371285043937107650, 371285043938740868, 371285043682515921, 371285043719052509, 371285043828532201, 371285043830160186, 371285043488089235, 371285042995565492, 371285042502387375, 371285042428489958]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362466424511583017, 362466458884225925⟩, ⟨905963386828113165, 907097111751844329⟩, true⟩

def words01 : List Nat := [371285042249293120, 371285042176008959, 371285042102194767, 371285042016518739, 371285041371717940, 371285040803607129, 371285040234636627, 371285040084662899, 371285039703647607, 371285039324859925]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482336056225161, 362482370443413883⟩, ⟨129191508458341183, 130325943582719177⟩, true⟩

def words02 : List Nat := [371285038983151475, 371285038984943451, 371285039108355206, 371285039380440985, 371285039583157781, 371285039584784234, 371285039246754188, 371285039266553037, 371285039414562552, 371285039416249901]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474136824876392, 362474171226919568⟩, ⟨529664959662243096, 530800120201849224⟩, true⟩

def words03 : List Nat := [371285039362809451, 371285039264343229, 371285039420438572, 371285039469549991, 371285039647750621, 371285039826552842, 371285039986945841, 371285039988572812, 371285039590735429, 371285039370248845]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362459926493468769, 362459960909995559⟩, ⟨1223751889485846923, 1224887757480804897⟩, true⟩

def words04 : List Nat := [371285039148840462, 371285039106329563, 371285038505393637, 371285037874852375, 371285037243729538, 371285036743123926, 371285036091974686, 371285035859366017, 371285035626198837, 371285035377907142]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488171042547860, 362488205473787136⟩, ⟨(-156195125311422026), (-155058538537397796)⟩, true⟩

def words05 : List Nat := [371285034865734399, 371285034570569470, 371285034274590922, 371285034145996629, 371285033616518351, 371285033015784892, 371285032414399301, 371285032231426386, 371285031944752570, 371285032011546548]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478164500505943, 362478198946440527⟩, ⟨332723076835298506, 333860381696315156⟩, true⟩

def words06 : List Nat := [371285032047088201, 371285032048726866, 371285031743403469, 371285031779660307, 371285031879847663, 371285031881475922, 371285031489605981, 371285031036812839, 371285030583387914, 371285030548275934]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464807234568949, 362464841695173848⟩, ⟨985665352213469343, 986803374087029461⟩, true⟩

def words07 : List Nat := [371285030687316495, 371285030966810637, 371285031160940592, 371285031162596959, 371285031007956200, 371285030830580331, 371285030799095689, 371285030800723925, 371285030391407214, 371285029980241095]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472255776878481, 362472290252073310⟩, ⟨621573934760624231, 622712669864289413⟩, true⟩

def words08 : List Nat := [371285029568356524, 371285029333285163, 371285028887813318, 371285028860324772, 371285028832333864, 371285028733363157, 371285028076802954, 371285027668254890, 371285027265520952, 371285027267206554]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471039218776862, 362471073708784025⟩, ⟨681063907774119526, 682203367128053290⟩, true⟩

def words09 : List Nat := [371285027007906195, 371285026727818210, 371285026447095414, 371285026444523981, 371285026280966229, 371285026068066760, 371285025854616099, 371285025642966707, 371285024981188421, 371285024697886849]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk488
