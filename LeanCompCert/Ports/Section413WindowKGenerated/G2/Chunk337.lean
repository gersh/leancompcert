import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk337

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567514605738292, 360567521503625384⟩, ⟨461691081107534139, 461848252694324225⟩, true⟩

def state01 : KState := ⟨⟨360629699127149442, 360629706029287494⟩, ⟨(-1634132100589005259), (-1633974785723679491)⟩, true⟩

def words00 : List Nat := [360581225996486975, 360581226775442380, 360581228433288452, 360581230091125338, 360581230925302497, 360581231388362981, 360581232346023027, 360581233303758062, 360581234513373961, 360581235951694908]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605399906247845, 360605406812681363⟩, ⟨(-814818367735458790), (-814660908048240742)⟩, true⟩

def words01 : List Nat := [360581236788481884, 360581237625275440, 360581239340462510, 360581241498907024, 360581243072856471, 360581244646783607, 360581245777809952, 360581246519141231, 360581247236009579, 360581247952978263]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360631152525368132, 360631159436048997⟩, ⟨(-1683300069891984104), (-1683142466962919626)⟩, true⟩

def words02 : List Nat := [360581249547883120, 360581250893197286, 360581251792175443, 360581252691145455, 360581253105709086, 360581254335691957, 360581256030281796, 360581257724858656, 360581258977030214, 360581260456861813]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360648580266920778, 360648587181862917⟩, ⟨(-2271346644242203194), (-2271188897558764736)⟩, true⟩

def words03 : List Nat := [360581262573562567, 360581264690274350, 360581266571335895, 360581267870061754, 360581268415116297, 360581268960171979, 360581269636354814, 360581270755001023, 360581272750517866, 360581274746026435]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360611255053574891, 360611261972818573⟩, ⟨(-1012123029574738592), (-1011965137736661148)⟩, true⟩

def words04 : List Nat := [360581276141825020, 360581276663193178, 360581277685884770, 360581278708648937, 360581279205232303, 360581279205683741, 360581279145257836, 360581278411458971, 360581277820069229, 360581278708982342]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360590643646390466, 360590650569879969⟩, ⟨(-316177134168445027), (-316019099012201031)⟩, true⟩

def words05 : List Nat := [360581280474261382, 360581282239522168, 360581283563186358, 360581284908589999, 360581285845808885, 360581286783091942, 360581288596504129, 360581289536419672, 360581289814110328, 360581290091842820]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360633674119514926, 360633681047273335⟩, ⟨(-1769320309815746006), (-1769162130520116540)⟩, true⟩

def words06 : List Nat := [360581290092216142, 360581290366754084, 360581291200466548, 360581292034215886, 360581292119921600, 360581292120373148, 360581291420709180, 360581291509139899, 360581292473201545, 360581294024960697]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611168621227292, 360611175553280012⟩, ⟨(-1009097593694148316), (-1008939269358031992)⟩, true⟩

def words07 : List Nat := [360581295135502181, 360581296246027263, 360581298231987248, 360581300778133898, 360581302710789799, 360581304643398030, 360581306118456654, 360581306720599538, 360581307605182204, 360581308489860989]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587367168953997, 360587374105266901⟩, ⟨(-204966059934523890), (-204807591668097606)⟩, true⟩

def words08 : List Nat := [360581309167540114, 360581310196873191, 360581310785461953, 360581311374065495, 360581311544314896, 360581312155063217, 360581312632116807, 360581313109226401, 360581313109635818, 360581313095185279]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360661346390137026, 360661353330714852⟩, ⟨(-2705156355552820740), (-2704997743153598734)⟩, true⟩

def words09 : List Nat := [360581314149698542, 360581315204284921, 360581316839361652, 360581317898819044, 360581318211905885, 360581318525014804, 360581319712485835, 360581321443043338, 360581323811216201, 360581326179353840]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk337
