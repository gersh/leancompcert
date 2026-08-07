import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk276

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360516128286069876, 360516132834965397⟩, ⟨1839305384081988167, 1839390303657837013⟩, true⟩

def state01 : KState := ⟨⟨360512539654584394, 360512544206906505⟩, ⟨1938168118965610702, 1938253133132666932⟩, true⟩

def words00 : List Nat := [360582774996912936, 360582772549847839, 360582769406131111, 360582765603657588, 360582761801400285, 360582757666183333, 360582754330772919, 360582751551191767, 360582748771764856, 360582745334510007]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581387500638205, 360581392056388821⟩, ⟨36864093689203940, 36949202534520118⟩, true⟩

def words01 : List Nat := [360582742792298373, 360582741557353321, 360582740322385977, 360582739956251331, 360582738283438169, 360582735362621970, 360582732441947836, 360582730827944472, 360582729874272843, 360582729826212664]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360541671121263153, 360541675680486546⟩, ⟨1133856347802368370, 1133941552582787642⟩, true⟩

def words02 : List Nat := [360582729778109426, 360582728740953620, 360582727756428391, 360582727367669428, 360582726978845122, 360582725597365896, 360582723675740959, 360582721097624832, 360582718519630896, 360582715910402681]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360511805750295852, 360511810312945505⟩, ⟨1959354488692338495, 1959439788157287665⟩, true⟩

def words03 : List Nat := [360582714425400487, 360582714245363979, 360582714065298513, 360582713074690986, 360582711391151242, 360582709376210787, 360582707361303024, 360582706031254968, 360582704331460934, 360582701766930936]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581405175433229, 360581409741524420⟩, ⟨35147456650418918, 35232851256479530⟩, true⟩

def words04 : List Nat := [360582699202504418, 360582697607946729, 360582696941030029, 360582695566313121, 360582694191667987, 360582691654173866, 360582688556653776, 360582686762665077, 360582684968695859, 360582683985692828]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360561463017846955, 360561467587404840⟩, ⟨586771120087561679, 586856610565270349⟩, true⟩

def words05 : List Nat := [360582683939935787, 360582683064136309, 360582682614992538, 360582684053773082, 360582685161966140, 360582686270138451, 360582686361523239, 360582686361887586, 360582685151274983, 360582684384605320]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360547214671006490, 360547219243995767⟩, ⟨980891754524843745, 980977339932189731⟩, true⟩

def words06 : List Nat := [360582683869565873, 360582683869930268, 360582682820166202, 360582681116175552, 360582679412242084, 360582676850955307, 360582675149012718, 360582674372748544, 360582673596501271, 360582671984867910]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577845655663485, 360577850232099314⟩, ⟨132969887675709105, 133055568465665427⟩, true⟩

def words07 : List Nat := [360582670703944332, 360582668958424626, 360582667212924604, 360582666768326972, 360582665488660186, 360582663010627591, 360582660532702274, 360582658432465906, 360582657326214798, 360582657152925386]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360512416787369475, 360512421367276419⟩, ⟨1943964764081808395, 1944050540969273225⟩, true⟩

def words08 : List Nat := [360582656979596170, 360582656152851721, 360582654026243325, 360582651858780841, 360582649691380316, 360582646629128329, 360582642654871116, 360582637684163994, 360582632713746272, 360582629043006621]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360486718075280622, 360486722658627218⟩, ⟨2655816261245805461, 2655902133394419981⟩, true⟩

def words09 : List Nat := [360582626507904872, 360582625272165990, 360582624036473546, 360582621893642216, 360582618948608468, 360582615372388273, 360582611796319703, 360582609519291473, 360582607063223890, 360582603602071060]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk276
