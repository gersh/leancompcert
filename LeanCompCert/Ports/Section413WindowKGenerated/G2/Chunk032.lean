import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk032

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360737395952696365, 360737396001959269⟩, ⟨(-485641849160011604), (-485641742065807042)⟩, true⟩

def state01 : KState := ⟨⟨360835991525362881, 360835991574954052⟩, ⟨(-805256526210927691), (-805256418064587761)⟩, true⟩

def words00 : List Nat := [360585680368729985, 360585645838767604, 360585515885356470, 360585481626734844, 360585447389482189, 360585387029018024, 360585336025122104, 360585236506874752, 360585137050645348, 360585211002526588]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨359912929976930985, 359912930026848606⟩, ⟨2162639076454793144, 2162639185650678182⟩, true⟩

def words01 : List Nat := [360585280562939964, 360585350080060593, 360585350080092263, 360585332908531668, 360585220923682037, 360585083313974929, 360584945789809484, 360584903109719978, 360584765747735006, 360584557103137637]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360352536790688499, 360352536840933663⟩, ⟨744686973047129183, 744687083299352971⟩, true⟩

def words02 : List Nat := [360584348588084653, 360584234828017978, 360584170993615819, 360584118733466563, 360584066505723790, 360583930307594372, 360583699835280816, 360583465080460937, 360583230471035168, 360583090117496931]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360172249178645835, 360172249229222612⟩, ⟨1328641813655947305, 1328641924980919625⟩, true⟩

def words03 : List Nat := [360583018760896594, 360582897410317378, 360582776134801557, 360582714029764131, 360582714029793293, 360582702553354321, 360582691084002478, 360582617704165577, 360582450502717998, 360582323897426600]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨359627557904161977, 359627557955068678⟩, ⟨3094370618138651215, 3094370730534235657⟩, true⟩

def words04 : List Nat := [360582197370251369, 360582066999216120, 360581842955762966, 360581553794997856, 360581264812446573, 360580902531954736, 360580590679648310, 360580303305926169, 360580016109099737, 360579672026002289]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360413829760777721, 360413829812015592⟩, ⟨534285205558956080, 534285319032531572⟩, true⟩

def words05 : List Nat := [360579379157968314, 360579179227940880, 360578979420823852, 360578872438477745, 360578672429846974, 360578388653566675, 360578105051535789, 360577914125280188, 360577771302937358, 360577721014172811]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360205937866574948, 360205937918148806⟩, ⟨1211987272363430047, 1211987386934015627⟩, true⟩

def words06 : List Nat := [360577670756245842, 360577573187650419, 360577484058443725, 360577416453508877, 360577348889976770, 360577257039810723, 360577140625021974, 360576953494013686, 360576766477487408, 360576576262776946]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨359923722171610861, 359923722223517570⟩, ⟨2137203809181711781, 2137203924842399005⟩, true⟩

def words07 : List Nat := [360576462952397592, 360576441344209613, 360576419749221694, 360576351413202813, 360576191182943136, 360576000176543342, 360575809286706313, 360575659936237010, 360575507500956545, 360575308785969521]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨359898913996607538, 359898914048849210⟩, ⟨2218869623548125036, 2218869740309161402⟩, true⟩

def words08 : List Nat := [360575110192105480, 360574936536012435, 360574812230157604, 360574670649479964, 360574529154998067, 360574309332814829, 360574055522728218, 360573835160208567, 360573614931678848, 360573342541344396]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨359979807465717581, 359979807518297875⟩, ⟨1951604237937682550, 1951604355814469264⟩, true⟩

def words09 : List Nat := [360573137610202389, 360572887085449680, 360572636712846234, 360572425703374711, 360572268348970159, 360572087488934882, 360571906738608141, 360571651308099163, 360571382042602252, 360571202777635593]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk032
