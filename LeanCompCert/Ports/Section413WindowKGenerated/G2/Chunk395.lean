import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk395

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360641298525597757, 360641308126374966⟩, ⟨(-2325594967169598441), (-2325338646996287841)⟩, true⟩

def state01 : KState := ⟨⟨360616713927983797, 360616723533864815⟩, ⟨(-1354652157460931244), (-1354395635662451406)⟩, true⟩

def words00 : List Nat := [360582441172946958, 360582441424622026, 360582442315778368, 360582443207046146, 360582443936089947, 360582444027845082, 360582444028323662, 360582443710802288, 360582443714579372, 360582444582796443]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578677258216169, 360578686869130796⟩, ⟨148525987435050220, 148782708137231030⟩, true⟩

def words01 : List Nat := [360582446090184630, 360582447597602421, 360582448784592911, 360582449685012602, 360582450150368850, 360582450615835654, 360582451480363894, 360582451707995830, 360582451708476728, 360582451613769896]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598943522246172, 360598953138216163⟩, ⟨(-652383472314531531), (-652126551799732491)⟩, true⟩

def words02 : List Nat := [360582452062762869, 360582453107192152, 360582454247757412, 360582455388364677, 360582455931809731, 360582455932344695, 360582455943098626, 360582456047891532, 360582456134075140, 360582456551947166]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585022348565315, 360585031969627484⟩, ⟨(-101987267488363287), (-101730145653997869)⟩, true⟩

def words03 : List Nat := [360582456649772798, 360582456747651974, 360582457033509163, 360582457818609561, 360582458441701391, 360582459064858177, 360582459271165823, 360582459271701058, 360582459127701042, 360582459193378680]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603512437234836, 360603522063344001⟩, ⟨(-833228208043368948), (-832970886625826126)⟩, true⟩

def words04 : List Nat := [360582459897166156, 360582460393522983, 360582460394007986, 360582460387479408, 360582460380866924, 360582459954679091, 360582460343662032, 360582460757588924, 360582460851992871, 360582461385064670]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360606903234715466, 360606912865875799⟩, ⟨(-967271791629827629), (-967014270413931963)⟩, true⟩

def words05 : List Nat := [360582462555946797, 360582463726926470, 360582465264698215, 360582466166554526, 360582466533107727, 360582466899683666, 360582467248189443, 360582468003527858, 360582468621882581, 360582469240325032]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599739062231574, 360599748698485230⟩, ⟨(-684028012502058371), (-683770289769156323)⟩, true⟩

def words06 : List Nat := [360582469539504555, 360582469540039974, 360582469878206148, 360582470366436335, 360582470542064739, 360582470542600258, 360582470277498202, 360582469532847125, 360582468788131234, 360582469117737482]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573801790192236, 360573811431495267⟩, ⟨342390022747127977, 342647945309076873⟩, true⟩

def words07 : List Nat := [360582469537043295, 360582469956425470, 360582470054235638, 360582470054771316, 360582469744942100, 360582469269832114, 360582468794588684, 360582468747356897, 360582468747833960, 360582468529658711]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596841890879153, 360596851537236705⟩, ⟨(-569533820203975566), (-569275697559467150)⟩, true⟩

def words08 : List Nat := [360582468729699768, 360582469473043671, 360582470513444922, 360582471553895558, 360582472007717039, 360582472008252872, 360582472021569989, 360582472216664734, 360582472256622141, 360582472620372785]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571297830594190, 360571307482067888⟩, ⟨441902435622711054, 442160760840240954⟩, true⟩

def words09 : List Nat := [360582472620854725, 360582472612175458, 360582472739765405, 360582473195847805, 360582473490101215, 360582473784428294, 360582473784905788, 360582473703072453, 360582473439193891, 360582473157846682]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk395
