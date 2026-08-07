import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk004

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨359296073113043532, 359296073114433170⟩, ⟨1225565292096187756, 1225565292475630264⟩, true⟩

def state01 : KState := ⟨⟨361776598547112923, 361776598548577382⟩, ⟨227250799786501662, 227250800196265628⟩, true⟩

def words00 : List Nat := [371152345664253372, 371150709723239639, 371146268544760053, 371145303736934364, 371144343693589437, 371142423043765816, 371136412619198180, 371132631595373691, 371130868792949765, 371130868792958518]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362773784270968760, 362773784272511626⟩, ⟨(-190451164930689158), (-190451164488372346)⟩, true⟩

def words01 : List Nat := [371129520203562536, 371128051779361836, 371126956554560043, 371126956554569503, 371124852304713439, 371124431811296444, 371124013334631576, 371123630343123968, 371120329118957187, 371121406209593877]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360121956209164690, 360121956210786404⟩, ⟨944140621752103685, 944140622227954903⟩, true⟩

def words02 : List Nat := [371127898198515973, 371127898198524789, 371127178381706219, 371126249640198387, 371125325269235514, 371124906422489536, 371121908462124630, 371120786609000867, 371119669985958836, 371117632076432811]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨364912976416627197, 364912976418331759⟩, ⟨(-1136255124821463289), (-1136255124309562775)⟩, true⟩

def words03 : List Nat := [371112667417201835, 371112796534382296, 371118102265106743, 371119597237893893, 371120152384785199, 371120704990961228, 371123888351988511, 371124695952917247, 371130578408526812, 371136434186337286]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨364195638368059996, 364195638369849750⟩, ⟨(-822159957513350472), (-822159956963522324)⟩, true⟩

def words04 : List Nat := [371141258792037859, 371142306484616238, 371148373263476998, 371154412775920522, 371161627934938167, 371162338914009217, 371162812335163725, 371163283647541478, 371168616243253298, 371172667290108016]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361114264164004523, 361114264165880811⟩, ⟨585053346326371249, 585053346915595007⟩, true⟩

def words05 : List Nat := [371178326287640311, 371183960300639725, 371189403507048381, 371189403507057999, 371188595981796041, 371187864559865387, 371191092911557774, 371191092911567481, 371188890194008566, 371186119267871235]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨363423905689963756, 363423905691929071⟩, ⟨(-476338495197287968), (-476338494566650876)⟩, true⟩

def words06 : List Nat := [371185221089249871, 371185815030034482, 371190986462366778, 371196135651983440, 371200785893851034, 371200785893861030, 371202636971640584, 371205812056977971, 371210419533266220, 371212571308560386]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨363011734364560440, 363011734366618630⟩, ⟨(-280170488880540652), (-280170488205771708)⟩, true⟩

def words07 : List Nat := [371214568278151523, 371216556803900063, 371220284957323087, 371221935651842525, 371224625253743259, 371227303578491097, 371229898116553014, 371229898116563297, 371228045849510601, 371229259339163804]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361344213743697843, 361344213745848729⟩, ⟨525429931977017096, 525429932696767344⟩, true⟩

def words08 : List Nat := [371232586458688406, 371232586458698752, 371230337286179521, 371227164870881580, 371224005537704774, 371221740020774525, 371217371268623339, 371217144590143869, 371216918838771287, 371216519730944173]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨363844523746704509, 363844523748950864⟩, ⟨(-710441261792656338), (-710441261025630346)⟩, true⟩

def words09 : List Nat := [371216222412275304, 371218101362622574, 371221749393698228, 371222355793318439, 371222355793326742, 371221730638794762, 371221888286955143, 371221888286966813, 371223641226887795, 371226477319757990]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk004
