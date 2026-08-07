import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk925

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569511015436892, 360569567377267072⟩, ⟨1146006761397226850, 1149527247986286202⟩, true⟩

def state01 : KState := ⟨⟨360606947097528571, 360607003471987823⟩, ⟨(-2317035518233578849), (-2313513863393391611)⟩, true⟩

def words00 : List Nat := [360581994565600506, 360581994552991620, 360581994694352678, 360581994835968230, 360581994866833734, 360581994868173820, 360581994937883258, 360581995032049599, 360581995213501870, 360581995485225240]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598695497857762, 360598751885076459⟩, ⟨(-1553606539404372606), (-1550083704124706648)⟩, true⟩

def words01 : List Nat := [360581995682877170, 360581995880681065, 360581996162996097, 360581996528301600, 360581996864035002, 360581997199979636, 360581997477110748, 360581997662175878, 360581997844364096, 360581998026988839]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590297030869044, 360590353430688675⟩, ⟨(-776616970966209976), (-773092969784482462)⟩, true⟩

def words02 : List Nat := [360581998172234854, 360581998201207549, 360581998202399875, 360581998172727056, 360581998142837838, 360581998113197515, 360581998227171430, 360581998341399315, 360581998377211198, 360581998468894418]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595276309669857, 360595332722145444⟩, ⟨(-1237410164963831719), (-1233884992665426315)⟩, true⟩

def words03 : List Nat := [360581998599847214, 360581998731197434, 360581998859547808, 360581998953776109, 360581998955011548, 360581998955876913, 360581998961752777, 360581999044200306, 360581999189368856, 360581999334861263]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568265483649864, 360568321908868448⟩, ⟨1262211799132119794, 1265738150730522680⟩, true⟩

def words04 : List Nat := [360581999420952147, 360581999422290854, 360581999391805585, 360581999349737708, 360581999307315843, 360581999218205418, 360581999012522519, 360581998715361229, 360581998417948483, 360581998171977368]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360570099110762579, 360570155548586745⟩, ⟨1092569854265166762, 1096097372573704960⟩, true⟩

def words05 : List Nat := [360581998025289565, 360581997995484098, 360581997965531324, 360581997877154590, 360581997851326340, 360581997783302210, 360581997761967287, 360581997763306218, 360581997695148940, 360581997568601587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589977521280767, 360590033971758921⟩, ⟨(-747516211283162150), (-743987521659601270)⟩, true⟩

def words06 : List Nat := [360581997441765655, 360581997311643644, 360581997259489164, 360581997280891062, 360581997282149498, 360581997177465867, 360581997002705895, 360581996944954418, 360581996944104382, 360581997032310718]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579822224828713, 360579878688051820⟩, ⟨192598740846044087, 196128610332983221⟩, true⟩

def words07 : List Nat := [360581997049401374, 360581997066637559, 360581997118642830, 360581997247210064, 360581997278306935, 360581997309608187, 360581997310801188, 360581997283524485, 360581997186511457, 360581997165156303]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587193706705396, 360587250182558307⟩, ⟨(-489835663469139824), (-486304624652037632)⟩, true⟩

def words08 : List Nat := [360581997237020479, 360581997383248439, 360581997466325118, 360581997549533853, 360581997603353832, 360581997731581553, 360581997832219818, 360581997933103094, 360581997944162460, 360581998002274565]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597108379595557, 360597164868093843⟩, ⟨(-1407863668447805923), (-1404331458733571685)⟩, true⟩

def words09 : List Nat := [360581998141868991, 360581998281867448, 360581998537973270, 360581998711965947, 360581998786669913, 360581998861499798, 360581998946897375, 360581999135328799, 360581999300196468, 360581999465358089]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk925
