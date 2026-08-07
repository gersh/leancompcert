import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk643

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572767593078541, 360572794060538156⟩, ⟨647949167569213758, 649098801304266406⟩, true⟩

def state01 : KState := ⟨⟨360625271172673328, 360625297648680199⟩, ⟨(-2728226599455506937), (-2727076416089312657)⟩, true⟩

def words00 : List Nat := [360582888838054369, 360582889111217599, 360582889625684416, 360582890140308422, 360582890445206013, 360582890814150501, 360582891371032653, 360582891928164192, 360582892478779157, 360582893139092581]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360613083907438985, 360613110392063501⟩, ⟨(-1944415136038505887), (-1943264398428700453)⟩, true⟩

def words01 : List Nat := [360582893600979479, 360582894062944678, 360582894703153822, 360582895468974463, 360582896123208998, 360582896777584864, 360582897247392152, 360582897476565773, 360582897947025806, 360582898417771611]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624070937440096, 360624097430602774⟩, ⟨(-2651211831831852655), (-2650060545005807571)⟩, true⟩

def words02 : List Nat := [360582899080274327, 360582899612348454, 360582899957268621, 360582900302259403, 360582900537504859, 360582900921234300, 360582901546093040, 360582902171114514, 360582902644246076, 360582903285555973]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360629314597815623, 360629341099517678⟩, ⟨(-2988526758259992890), (-2987374922051957980)⟩, true⟩

def words03 : List Nat := [360582904040798718, 360582904796291665, 360582905792853981, 360582906684254310, 360582907371278732, 360582908058352272, 360582908622787708, 360582909308072965, 360582910030472852, 360582910753050388]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610506414966825, 360610532925302025⟩, ⟨(-1778459260774918842), (-1777306869070235330)⟩, true⟩

def words04 : List Nat := [360582911354082736, 360582911794516373, 360582912315646583, 360582912837042773, 360582913214195492, 360582913350996934, 360582913351803733, 360582913352293982, 360582913547881986, 360582913978136166]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360588054194956859, 360588080713821119⟩, ⟨(-333588064682359205), (-332435124089140729)⟩, true⟩

def words05 : List Nat := [360582914330092304, 360582914682197437, 360582914890464534, 360582914990521572, 360582914991279726, 360582914991305479, 360582915185715553, 360582915387497872, 360582915468569084, 360582915549760755]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606358155269667, 360606384682680645⟩, ⟨(-1511762509815296405), (-1510609019112546279)⟩, true⟩

def words06 : List Nat := [360582915668190011, 360582915956695981, 360582916315795405, 360582916675053563, 360582916803161741, 360582916804067582, 360582916768993741, 360582916847272754, 360582917087846162, 360582917453352026]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582642817714477, 360582669353767040⟩, ⟨15007995213999449, 16162042216782367⟩, true⟩

def words07 : List Nat := [360582917676215145, 360582917899193795, 360582918363028266, 360582918947594937, 360582919448432205, 360582919949404958, 360582920293410874, 360582920397236077, 360582920397983460, 360582920395118653]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579491997814922, 360579518542398125⟩, ⟨217846515088374206, 219001111336101664⟩, true⟩

def words08 : List Nat := [360582920629066622, 360582920629972658, 360582920627647398, 360582920441554462, 360582920255319764, 360582919969580620, 360582919872185306, 360582919871156318, 360582919870032514, 360582919708904355]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604260120780886, 360604286673928880⟩, ⟨(-1377181003570011532), (-1376025855793105470)⟩, true⟩

def words09 : List Nat := [360582919708406434, 360582919760991537, 360582919807108272, 360582919815688511, 360582919816533074, 360582919616789501, 360582919416876385, 360582919479335800, 360582919811857326, 360582920144592487]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk643
