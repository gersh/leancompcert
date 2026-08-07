import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk822

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494093054999594, 362494194586231169⟩, ⟨(-741448620938037987), (-735813170621042191)⟩, true⟩

def state01 : KState := ⟨⟨362482599304645437, 362482700861267830⟩, ⟨203393168567750567, 209030706143631929⟩, true⟩

def words00 : List Nat := [371285243368342237, 371285243381276178, 371285243383420912, 371285243366261968, 371285243349219352, 371285243352387426, 371285243357306893, 371285243436003724, 371285243501624874, 371285243504573312]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362508520995427687, 362508622577756967⟩, ⟨(-1927765327413526710), (-1922125676347663398)⟩, true⟩

def words01 : List Nat := [371285243575408002, 371285243678642502, 371285243889317578, 371285243989284026, 371285244047628129, 371285244106820436, 371285244312825131, 371285244452309952, 371285244738578182, 371285245026081025]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491905168916969, 362492006776982708⟩, ⟨(-561514655599209021), (-555872888349953993)⟩, true⟩

def words02 : List Nat := [371285245312393475, 371285245476690293, 371285245787996913, 371285246100844305, 371285246391911451, 371285246486631589, 371285246580500821, 371285246675304620, 371285246796980152, 371285246882437465]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491756084222594, 362491857717974374⟩, ⟨(-549212486934274345), (-543568607392497769)⟩, true⟩

def words03 : List Nat := [371285247114526984, 371285247347802672, 371285247579779710, 371285247615326360, 371285247695303998, 371285247776740533, 371285248004574889, 371285248091771226, 371285248174271285, 371285248257882784]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362502833359344260, 362502935018628448⟩, ⟨(-1460250482474046359), (-1454604503018292573)⟩, true⟩

def words04 : List Nat := [371285248488104006, 371285248645859506, 371285248854714952, 371285249064666833, 371285249249761883, 371285249311637424, 371285249447821165, 371285249585496932, 371285249854491312, 371285250072512069]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362506970394876044, 362507072080101469⟩, ⟨(-1800537174602384176), (-1794889061347118400)⟩, true⟩

def words05 : List Nat := [371285250273163750, 371285250474711057, 371285250808183006, 371285251069099015, 371285251374128261, 371285251680280515, 371285251957260233, 371285252102823466, 371285252370013249, 371285252638794567]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362503133227994685, 362503234938594872⟩, ⟨(-1484856958976725888), (-1479206758261347198)⟩, true⟩

def words06 : List Nat := [371285253053817715, 371285253272757349, 371285253474112808, 371285253676515316, 371285253922988070, 371285254096870725, 371285254417369222, 371285254738994553, 371285255030954861, 371285255252456849]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362515435993578250, 362515537730028255⟩, ⟨(-2497105424578519115), (-2491453097072655475)⟩, true⟩

def words07 : List Nat := [371285255505061449, 371285255759142567, 371285256123389072, 371285256322578791, 371285256500361250, 371285256678999145, 371285256954726586, 371285257178194332, 371285257548145873, 371285257919414959]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362497138432050792, 362497240194175143⟩, ⟨(-991514591559038764), (-985860151434953058)⟩, true⟩

def words08 : List Nat := [371285258289363566, 371285258463129937, 371285258769097886, 371285259076505836, 371285259389864446, 371285259507156393, 371285259603053154, 371285259699928722, 371285259875541463, 371285260024394305]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480267865028120, 362480369652824227⟩, ⟨396905030142483374, 402561582925860846⟩, true⟩

def words09 : List Nat := [371285260247087130, 371285260470949622, 371285260693650973, 371285260757843729, 371285260858331660, 371285260960289003, 371285261127684139, 371285261130535494, 371285261101337293, 371285261045083351]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk822
