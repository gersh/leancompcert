import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk008

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361000403249862782, 361000403252445137⟩, ⟨(-411933333358337970), (-411933331945999998)⟩, true⟩

def state01 : KState := ⟨⟨359671235595329318, 359671235597982480⟩, ⟨643244016416902160, 643244017886242706⟩, true⟩

def words00 : List Nat := [360486129429797592, 360485924313330323, 360484264972859600, 360482629189442731, 360480997470082308, 360478086963145420, 360475134688445903, 360471383864795326, 360467642313884189, 360465364015125990]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨358060471263627211, 358060471266351614⟩, ⟨1966526155553058172, 1966526157080465446⟩, true⟩

def words01 : List Nat := [360464858633967690, 360465331283781939, 360465331283788654, 360465014279458060, 360464885795395780, 360464272342715176, 360463660391752657, 360463327162545489, 360461602105269881, 360458673896937548]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362786809670876422, 362786809673672795⟩, ⟨(-1932890518828766186), (-1932890517241977158)⟩, true⟩

def words02 : List Nat := [360455752821876049, 360454248905297331, 360454259616989987, 360454967497637967, 360454967497645037, 360454229331222127, 360454735371327343, 360455685016369506, 360458025917951682, 360460828305150561]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361315002901738835, 361315002904608554⟩, ⟨(-706705592360281081), (-706705590712240189)⟩, true⟩

def words03 : List Nat := [360462880272717917, 360464927313593304, 360466381484440706, 360468581529846100, 360470334302851835, 360472082887631857, 360473040649524496, 360473040649532206, 360473686725180373, 360474687101145724]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨359797898795400321, 359797898798342985⟩, ⟨572870424182236909, 572870425891921623⟩, true⟩

def words04 : List Nat := [360476471339229939, 360476944918996663, 360476944919003563, 360476704253442548, 360476464157502967, 360475470801058680, 360475269085161795, 360474363041317623, 360473459131851543, 360471864005274658]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨363520183126719490, 363520183129735940⟩, ⟨(-2616116265258315936), (-2616116263485541516)⟩, true⟩

def words05 : List Nat := [360471072036765230, 360470491927299741, 360470645587240830, 360471606308245286, 360471606308252550, 360471436043886714, 360472397498643886, 360474646152439104, 360478187474512096, 360481720570519284]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361338779224087476, 361338779227179441⟩, ⟨(-736596058918148658), (-736596057080046640)⟩, true⟩

def words06 : List Nat := [360484084218546695, 360485190914544700, 360487586058241700, 360489975664036521, 360491955050514816, 360492683773389124, 360492683773396223, 360492490683390368, 360492298037778838, 360493089150164463]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359422011886321423, 359422011889488783⟩, ⟨943002642509521724, 943002644413604592⟩, true⟩

def words07 : List Nat := [360494207955445515, 360495324197600274, 360495657938855002, 360495947039075396, 360495947039082211, 360495346661337856, 360495395241211365, 360495395241219393, 360494824909291135, 360493605803595152]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361724720760175739, 361724720763419558⟩, ⟨(-1088293951508079946), (-1088293949536329652)⟩, true⟩

def words08 : List Nat := [360492410584328863, 360493418743312087, 360495656638176308, 360497889475652590, 360498953250978178, 360498953250986295, 360499901163604323, 360500985614486978, 360501918572920887, 360503290965960154]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨359802372059009859, 359802372062331880⟩, ⟨633630167064194925, 633630169105941837⟩, true⟩

def words09 : List Nat := [360503709359645821, 360504126816280364, 360504812863980148, 360506189040919424, 360507188606832015, 360508185944059549, 360508270111772743, 360508270111781009, 360507188713163305, 360506405583560705]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk008
