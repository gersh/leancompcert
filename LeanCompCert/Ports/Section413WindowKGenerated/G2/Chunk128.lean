import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk128

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587510339846492, 360587511252542314⟩, ⟨(-84697499533938231), (-84689586117347121)⟩, true⟩

def state01 : KState := ⟨⟨360503537782261700, 360503538696460580⟩, ⟨989596671490902330, 989604604153878668⟩, true⟩

def words00 : List Nat := [360580895395631488, 360580891497006882, 360580884618314637, 360580875484530607, 360580866352131321, 360580853818719739, 360580839033638000, 360580821065277793, 360580803099693227, 360580791202639650]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360395036157151674, 360395037072835804⟩, ⟨2380125529516414917, 2380133481213065789⟩, true⟩

def words01 : List Nat := [360580785172597681, 360580781716367056, 360580778260658753, 360580771771640283, 360580762169712528, 360580748461159288, 360580734754699954, 360580720850108548, 360580709393541002, 360580694910683938]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360674720453496852, 360674721370670197⟩, ⟨(-1206756234788538791), (-1206748263992631793)⟩, true⟩

def words02 : List Nat := [360580680430050707, 360580672004554430, 360580667359570817, 360580668063429457, 360580668063576836, 360580663745223038, 360580659560060258, 360580659227284545, 360580664607919743, 360580671938514276]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360645283823993653, 360645284742674488⟩, ⟨(-829120432980765388), (-829112442836484244)⟩, true⟩

def words03 : List Nat := [360580674341163476, 360580676743452492, 360580682433817765, 360580692164067623, 360580698054326312, 360580703943692692, 360580705184896881, 360580707092795788, 360580712122335940, 360580717151144508]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360613074037918036, 360613074958088227⟩, ⟨(-415467166017948455), (-415459156742699349)⟩, true⟩

def words04 : List Nat := [360580728214005031, 360580733247397961, 360580735116709832, 360580736985747652, 360580736985882414, 360580735274037057, 360580739023522671, 360580742772455701, 360580743506037745, 360580746022072143]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360571218811390038, 360571219733057468⟩, ⟨122960888383990895, 122968916906159219⟩, true⟩

def words05 : List Nat := [360580752479398703, 360580758935771497, 360580771413801558, 360580777872922395, 360580779128615569, 360580780384125880, 360580780384255011, 360580782600551754, 360580782600683137, 360580781857233686]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360548996431684881, 360548997354863548⟩, ⟨408223915648770072, 408231963612680078⟩, true⟩

def words06 : List Nat := [360580781113878510, 360580777224318434, 360580769910277272, 360580765166355223, 360580760423129218, 360580752941231442, 360580745740131795, 360580735531125562, 360580725323676177, 360580717010155909]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360435797236667289, 360435798161341165⟩, ⟨1865906722334264823, 1865914789548966893⟩, true⟩

def words07 : List Nat := [360580715911680406, 360580717277450996, 360580717277594795, 360580713917056967, 360580707648404468, 360580699294088672, 360580690941024250, 360580686445685761, 360580678570332280, 360580667322020433]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360517356786865403, 360517357713037717⟩, ⟨814859690158116176, 814867776680344960⟩, true⟩

def words08 : List Nat := [360580656075417438, 360580645646530154, 360580638849805490, 360580633711905918, 360580628574791419, 360580618276727227, 360580606247205356, 360580593754582796, 360580581263851122, 360580574763206868]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556214279036230, 360556215206721266⟩, ⟨313855713788703964, 313863819817500406⟩, true⟩

def words09 : List Nat := [360580569859380579, 360580561959130203, 360580554060074154, 360580554939778760, 360580556162982825, 360580557386023871, 360580557386166800, 360580555487988631, 360580547621441923, 360580545735389290]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk128
