import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk092

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360662592311491961, 360662592768073185⟩, ⟨(-799662305014761437), (-799659457271922331)⟩, true⟩

def state01 : KState := ⟨⟨360594343321771172, 360594343779402015⟩, ⟨(-172226629103572738), (-172223771698965166)⟩, true⟩

def words00 : List Nat := [360575686222622051, 360575686222732387, 360575692817620812, 360575701973441282, 360575702732889314, 360575702732999679, 360575691825843917, 360575672019845671, 360575652218128002, 360575646160066551]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360429905345427721, 360429905804100851⟩, ⟨1343467631837873945, 1343470498847246873⟩, true⟩

def words01 : List Nat := [360575655229842615, 360575664297672593, 360575665579910878, 360575665580021633, 360575663644481579, 360575654994838905, 360575646347040587, 360575640902730973, 360575634245124087, 360575618439550661]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360749128734308165, 360749129194025272⟩, ⟨(-1601242640173598851), (-1601239763533579025)⟩, true⟩

def words02 : List Nat := [360575602637380769, 360575602137449604, 360575610789979755, 360575619440654876, 360575619440757854, 360575617303960860, 360575625611268118, 360575635596442154, 360575647096019352, 360575665889558413]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360708207674215557, 360708208134988811⟩, ⟨(-1223745220705451475), (-1223742334312014283)⟩, true⟩

def words03 : List Nat := [360575676514222199, 360575687136596400, 360575697372277629, 360575714671568492, 360575728900241089, 360575743125850870, 360575751450146694, 360575754153353097, 360575768488289417, 360575782820162276]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360661154591344336, 360661155053160472⟩, ⟨(-788870224351437516), (-788867328316454134)⟩, true⟩

def words04 : List Nat := [360575808778730614, 360575823158965885, 360575829783843900, 360575836407299497, 360575838329383223, 360575848517854359, 360575858337650423, 360575868155342885, 360575872098633046, 360575881317530113]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360830040609579259, 360830041072442392⟩, ⟨(-2352529424381791850), (-2352526518656755450)⟩, true⟩

def words05 : List Nat := [360575888779991358, 360575896240872111, 360575908497369960, 360575921176320709, 360575923880996457, 360575926585097164, 360575940875871795, 360575961093983274, 360575988532515869, 360576015965147634]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360685869591771533, 360685870055694834⟩, ⟨(-1017208705342094000), (-1017205789794796496)⟩, true⟩

def words06 : List Nat := [360576034429480823, 360576051630362961, 360576075445277205, 360576099255082709, 360576116039369947, 360576127082622439, 360576132277372763, 360576137471016200, 360576139118156943, 360576150954217670]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360431016190301370, 360431016655271145⟩, ⟨1346879659941409661, 1346882585194903929⟩, true⟩

def words07 : List Nat := [360576170064553144, 360576189170788224, 360576199457202618, 360576199457313878, 360576198257498347, 360576188418701499, 360576180283805435, 360576180283916713, 360576170506346333, 360576154864882665]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360622389517403750, 360622389983426272⟩, ⟨(-429228935950981587), (-429226000922866221)⟩, true⟩

def words08 : List Nat := [360576139226764744, 360576141263238300, 360576158930725050, 360576176594428058, 360576184393697143, 360576184393808538, 360576182926195120, 360576185122123165, 360576186969218198, 360576191942211886]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360496413771018249, 360496414238102035⟩, ⟨742004460905188188, 742007405797758354⟩, true⟩

def words09 : List Nat := [360576191942311388, 360576189376156817, 360576195748379286, 360576210534335694, 360576215805008208, 360576221074565840, 360576221074666061, 360576220532074173, 360576208560568644, 360576199980660934]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk092
