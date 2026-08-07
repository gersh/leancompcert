import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk287

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360665608949230890, 360665613884479326⟩, ⟨(-2385103940183948340), (-2385008143300395944)⟩, true⟩

def state01 : KState := ⟨⟨360651634649436014, 360651639588297332⟩, ⟨(-1984204160900041499), (-1984108260309457045)⟩, true⟩

def words00 : List Nat := [360582517737597142, 360582519167223011, 360582521807416820, 360582524447539990, 360582526779340746, 360582528408888195, 360582529091180760, 360582529773461416, 360582530975517215, 360582533382999382]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615744355953002, 360615749298381367⟩, ⟨(-953386898241501602), (-953290895222649158)⟩, true⟩

def words01 : List Nat := [360582537000236161, 360582540617293678, 360582543365544095, 360582546173648363, 360582548673990088, 360582551174257877, 360582553789737816, 360582555561959956, 360582556718071723, 360582557874154403]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360674397100104804, 360674402046120716⟩, ⟨(-2638420484042033311), (-2638324377971485347)⟩, true⟩

def words02 : List Nat := [360582558378628319, 360582559492979802, 360582561816327998, 360582564139587076, 360582565422083142, 360582565938748301, 360582567009091752, 360582568079483440, 360582570358361189, 360582573555014542]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360631410156798573, 360631415106422854⟩, ⟨(-1403143423082198988), (-1403047213324969330)⟩, true⟩

def words03 : List Nat := [360582575988490746, 360582578421841419, 360582581647354957, 360582585481425448, 360582588466000800, 360582591450424853, 360582593718944767, 360582594784401100, 360582596483397388, 360582598182400553]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360611975674642840, 360611980627848678⟩, ⟨(-844451184545015056), (-844354871835971470)⟩, true⟩

def words04 : List Nat := [360582600577345685, 360582603015518256, 360582604387025966, 360582605758475852, 360582606823295378, 360582608497420841, 360582609930562259, 360582611363675046, 360582611762347448, 360582612784231553]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360723426140393564, 360723431097181925⟩, ⟨(-4049248455616970333), (-4049152039892616241)⟩, true⟩

def words05 : List Nat := [360582615012705529, 360582617241135454, 360582620675963320, 360582623934252110, 360582626131184080, 360582628327997678, 360582631410734482, 360582635100797109, 360582639996653616, 360582644892255372]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360663344779652136, 360663349740063991⟩, ⟨(-2321301945897605035), (-2321205425944092295)⟩, true⟩

def words06 : List Nat := [360582649183086968, 360582652638174815, 360582656013802225, 360582659389305615, 360582661968752567, 360582664044282723, 360582665342799712, 360582666641268353, 360582668285819605, 360582671090522992]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576904115934833, 360576909079920847⟩, ⟨166271939690307215, 166368562490962993⟩, true⟩

def words07 : List Nat := [360582675100122464, 360582679109515856, 360582682343725464, 360582684378486643, 360582686094084114, 360582687809665166, 360582689494718999, 360582689980627095, 360582689980965812, 360582689780493848]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360638437104976944, 360638442072551664⟩, ⟨(-1604956124082520628), (-1604859397981296136)⟩, true⟩

def words08 : List Nat := [360582689780762881, 360582690845337125, 360582692802217700, 360582694759041440, 360582695674240319, 360582695932702063, 360582696364653774, 360582696796684585, 360582698432075494, 360582700368617057]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360669522748634778, 360669527719840551⟩, ⟨(-2500203981581323259), (-2500107150924109241)⟩, true⟩

def words09 : List Nat := [360582701380867574, 360582702393080420, 360582704608400828, 360582707428505108, 360582709581552818, 360582711734512039, 360582713117514326, 360582715428705324, 360582718443328963, 360582721457873116]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk287
