import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk082

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360257773651188147, 360257774009634543⟩, ⟨2643671203167499467, 2643673196104286843⟩, true⟩

def state01 : KState := ⟨⟨360519984987260727, 360519985346623895⟩, ⟨491999407560693583, 492001408019644593⟩, true⟩

def words00 : List Nat := [360580133867792038, 360580103094191203, 360580079964009166, 360580060877127195, 360580041794888416, 360580009716249839, 360579976112411483, 360579949984367525, 360579923862659984, 360579912436516666]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360525331880755656, 360525332241046937⟩, ⟨447515234609146378, 447517242692485618⟩, true⟩

def words01 : List Nat := [360579905138213895, 360579884072217636, 360579863011332884, 360579850157236875, 360579846752457777, 360579835821654869, 360579824893502732, 360579802635213923, 360579781351861211, 360579774727992495]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360440886162268633, 360440886523477481⟩, ⟨1142070798041554894, 1142072813671940832⟩, true⟩

def words02 : List Nat := [360579776135690553, 360579776135788006, 360579769502966370, 360579755512518332, 360579741525457917, 360579716772873932, 360579699549196617, 360579688241727986, 360579676936996445, 360579656002659977]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360641566380897863, 360641566743028314⟩, ⟨(-510007940058560448), (-510005916838792162)⟩, true⟩

def words03 : List Nat := [360579639143368475, 360579636903356414, 360579647036463083, 360579653790406901, 360579653790497635, 360579647481703111, 360579649469622371, 360579665308589942, 360579672820980886, 360579680331568687]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360753592892964967, 360753593256026046⟩, ⟨(-1434703759150689241), (-1434701728258007821)⟩, true⟩

def words04 : List Nat := [360579680331655720, 360579677444676984, 360579678949579952, 360579686995326260, 360579686995408382, 360579689230704754, 360579689230791831, 360579686313541594, 360579690016125249, 360579711092863035]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360393631268869582, 360393631632852617⟩, ⟨1537200043685434427, 1537202082188967727⟩, true⟩

def words05 : List Nat := [360579739190784097, 360579767281914545, 360579783798426595, 360579785775245740, 360579785775328125, 360579778922112882, 360579772070529484, 360579771356033815, 360579756112975961, 360579733579848861]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360542022965897475, 360542023330805489⟩, ⟨310782617090967434, 310784663239387878⟩, true⟩

def words06 : List Nat := [360579711052154038, 360579690475553365, 360579684129130836, 360579688210458053, 360579688210548584, 360579680222319437, 360579657728303347, 360579634683585187, 360579611644412053, 360579603096614363]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360499720577871920, 360499720943714829⟩, ⟨661268765322732417, 661270819207390721⟩, true⟩

def words07 : List Nat := [360579598553144837, 360579586484343790, 360579576830686461, 360579590215427488, 360579599175611557, 360579608133646357, 360579608410363348, 360579608410461548, 360579594215640671, 360579584569222968]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360427067795931377, 360427068162700705⟩, ⟨1262450907230655383, 1262452968790800867⟩, true⟩

def words08 : List Nat := [360579574925103654, 360579559477517265, 360579537927597774, 360579504961070345, 360579472002484971, 360579435358401191, 360579406189923856, 360579391457163634, 360579376727946651, 360579354407428184]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360865323419226258, 360865323786924327⟩, ⟨(-2372792244481163549), (-2372790175217113259)⟩, true⟩

def words09 : List Nat := [360579336039850823, 360579332094981704, 360579338622763613, 360579356640529557, 360579361195936589, 360579365750252147, 360579384705970257, 360579411005055889, 360579445452458855, 360579479891584355]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk082
