import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk780

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596324209786191, 360596363759171521⟩, ⟨(-1105026184650428170), (-1102942677796248810)⟩, true⟩

def state01 : KState := ⟨⟨360590585719873874, 360590625279753361⟩, ⟨(-657497936545519243), (-655413611094020513)⟩, true⟩

def words00 : List Nat := [360582223745489001, 360582223746603240, 360582223740194210, 360582223646670274, 360582223552967263, 360582223418432769, 360582223476163893, 360582223587766085, 360582223617131586, 360582223725984098]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609332724297644, 360609372294693768⟩, ⟨(-2120095301999127974), (-2118010156092959944)⟩, true⟩

def words01 : List Nat := [360582223970430869, 360582224215218082, 360582224427117399, 360582224568842113, 360582224569887626, 360582224557445519, 360582224695298417, 360582224929098149, 360582225277953047, 360582225627051814]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595348927521271, 360595388508553604⟩, ⟨(-1029070588003171034), (-1026984612208416358)⟩, true⟩

def words02 : List Nat := [360582225892837604, 360582226162957841, 360582226400622491, 360582226638601506, 360582226833615599, 360582226980229904, 360582227034351391, 360582227088592086, 360582227099958503, 360582227269915007]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580253073070981, 360580292664596387⟩, ⟨149024972009827210, 151111766631924982⟩, true⟩

def words03 : List Nat := [360582227603499393, 360582227937288549, 360582228152527830, 360582228343289014, 360582228492763433, 360582228642550609, 360582228915358770, 360582229024593799, 360582229025603211, 360582229001944311]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600009425981868, 360600049028036467⟩, ⟨(-1392885125165726196), (-1390797508792826736)⟩, true⟩

def words04 : List Nat := [360582229117195682, 360582229339561787, 360582229557734944, 360582229776100213, 360582229828105328, 360582229829219698, 360582229717343749, 360582229661510568, 360582229712206796, 360582229941685328]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360599098737069141, 360599138349732792⟩, ⟨(-1321809158320378902), (-1319720713858816944)⟩, true⟩

def words05 : List Nat := [360582230088960348, 360582230236360757, 360582230507732802, 360582230861360246, 360582231147882702, 360582231434586841, 360582231585827820, 360582231639636024, 360582231857123266, 360582232074975118]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593819284274554, 360593858907435120⟩, ⟨(-909664535712421414), (-907575271809106588)⟩, true⟩

def words06 : List Nat := [360582232425630603, 360582232699848944, 360582232891959988, 360582233084210449, 360582233185673645, 360582233369879816, 360582233530088679, 360582233690501390, 360582233758697504, 360582233908756878]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613321159908115, 360613360793608232⟩, ⟨(-2432390689887499395), (-2430300603111016941)⟩, true⟩

def words07 : List Nat := [360582234000247815, 360582234092045809, 360582234306532179, 360582234400246622, 360582234401285847, 360582234351048170, 360582234380638739, 360582234616740951, 360582235016287068, 360582235416075785]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580160700197048, 360580200344509621⟩, ⟨156868766504001709, 158959681952183535⟩, true⟩

def words08 : List Nat := [360582235700910811, 360582235822275907, 360582236078474141, 360582236335005626, 360582236440638792, 360582236441753807, 360582236383853945, 360582236244139312, 360582236104221280, 360582235940385562]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554312379542485, 360554352034371856⟩, ⟨2175520468211328010, 2177612204970007910⟩, true⟩

def words09 : List Nat := [360582235937878903, 360582235961667204, 360582235962670252, 360582235903508728, 360582235680624134, 360582235417019435, 360582235153095150, 360582234978314817, 360582234748799432, 360582234392950218]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk780
