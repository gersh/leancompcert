import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk241

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582493640279289, 360582497067694110⟩, ⟨(-331138799538716), (-275257276225312)⟩, true⟩

def state01 : KState := ⟨⟨360674960979627894, 360674964410012082⟩, ⟨(-2229465673466621053), (-2229409720367045973)⟩, true⟩

def words00 : List Nat := [360582485646964482, 360582484982077128, 360582486945551790, 360582488908923858, 360582489415835658, 360582489416150582, 360582491062867123, 360582492746682384, 360582496150858121, 360582499986289838]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360658208756899998, 360658212190277394⟩, ⟨(-1825495033944192563), (-1825439008663650659)⟩, true⟩

def words01 : List Nat := [360582502695690181, 360582505404898587, 360582509833990081, 360582515121629025, 360582518894704073, 360582522667511571, 360582525572072523, 360582527500882595, 360582530638976524, 360582533776917101]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360677961710639377, 360677965146982789⟩, ⟨(-2301984072164913739), (-2301927975329241283)⟩, true⟩

def words02 : List Nat := [360582538633320114, 360582543534932279, 360582546788790591, 360582550042410873, 360582552792054694, 360582556398274787, 360582560782689045, 360582565166801184, 360582568214401126, 360582572168020905]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360797235855109399, 360797239294420197⟩, ⟨(-5180748257790371920), (-5180692089336879306)⟩, true⟩

def words03 : List Nat := [360582577212729326, 360582582257111346, 360582589017880373, 360582595525241134, 360582600580383060, 360582605635136039, 360582612405963691, 360582620126129810, 360582629016987934, 360582637907181190]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360675829658474579, 360675833100786085⟩, ⟨(-2249730271308186680), (-2249674030403045188)⟩, true⟩

def words04 : List Nat := [360582645715045515, 360582651820378669, 360582657862301122, 360582663903810497, 360582668820767672, 360582672035729420, 360582674383271225, 360582676730650275, 360582678896263129, 360582682753785835]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596976776142276, 360596980221417627⟩, ⟨(-344723129944953498), (-344666817448094106)⟩, true⟩

def words05 : List Nat := [360582688325660012, 360582693897132783, 360582698410065729, 360582702451847375, 360582706051243258, 360582709650429595, 360582712163400892, 360582713619650233, 360582714210435909, 360582714801217797]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360648759813061727, 360648763261308576⟩, ⟨(-1596016645871793723), (-1595960261568736147)⟩, true⟩

def words06 : List Nat := [360582716354043599, 360582718760145742, 360582722340187614, 360582725919998544, 360582728043718343, 360582729146427354, 360582729738212027, 360582730330037469, 360582732633694012, 360582735365831818]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360699169076239719, 360699172527491760⟩, ⟨(-2814915639252478417), (-2814859182299427993)⟩, true⟩

def words07 : List Nat := [360582736786917996, 360582738207916073, 360582740407345820, 360582743845404022, 360582746819621998, 360582749793644850, 360582751903623061, 360582755008273065, 360582759823148403, 360582764637731228]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360692323803817938, 360692327258034281⟩, ⟨(-2649373344311711143), (-2649316815666711213)⟩, true⟩

def words08 : List Nat := [360582771162218298, 360582776476231914, 360582780927248760, 360582785377929245, 360582788666235732, 360582793034106341, 360582797821035434, 360582802607628241, 360582806099557220, 360582810627234947]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360707399938134358, 360707403395332295⟩, ⟨(-3014263669292265584), (-3014207068507605958)⟩, true⟩

def words09 : List Nat := [360582815683362205, 360582820739172159, 360582826275246212, 360582830116630212, 360582832517246625, 360582834917689677, 360582839026185676, 360582844236575845, 360582849383908140, 360582854530884231]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk241
