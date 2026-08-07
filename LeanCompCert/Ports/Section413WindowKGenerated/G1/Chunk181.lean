import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk181

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362426069707066459, 362426074054936686⟩, ⟨1078997877584932597, 1079051106854618787⟩, true⟩

def state01 : KState := ⟨⟨362445226903965627, 362445231256828905⟩, ⟨732424776148888710, 732478095818358180⟩, true⟩

def words00 : List Nat := [371285686845042924, 371285685694923408, 371285683628947749, 371285683818790785, 371285683819223139, 371285683211551677, 371285679881399330, 371285678745877697, 371285677610202776, 371285677314024839]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362445591095199889, 362445595453141595⟩, ⟨725913892719784470, 725967304385448180⟩, true⟩

def words01 : List Nat := [371285675081210157, 371285672841159775, 371285670761213774, 371285670761827472, 371285669404731580, 371285668971674596, 371285668538479679, 371285667338740669, 371285662084402105, 371285659873913419]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479421036848403, 362479425399770743⟩, ⟨112854539538123380, 112908041477951252⟩, true⟩

def words02 : List Nat := [371285658495278001, 371285658495840109, 371285657364788061, 371285655647783774, 371285653930761175, 371285652803036723, 371285651430246468, 371285652264792600, 371285653090384310, 371285653090971954]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362516905415454525, 362516909783405731⟩, ⟨(-566660950173902366), (-566607357034244848)⟩, true⟩

def words03 : List Nat := [371285655444134793, 371285658140764721, 371285663876192796, 371285665562668087, 371285667135395512, 371285668708121406, 371285671517806006, 371285672814706021, 371285674537082616, 371285676259507697]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362503070255817931, 362503074628812076⟩, ⟨(-315806652923785437), (-315752968280732871)⟩, true⟩

def words04 : List Nat := [371285677972326823, 371285677972885339, 371285677638243832, 371285678989504193, 371285681042902717, 371285681043461395, 371285679658359935, 371285678017368279, 371285677770414503, 371285678729507315]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483247140524634, 362483251518552380⟩, ⟨44159085666382322, 44212861695463520⟩, true⟩

def words05 : List Nat := [371285680924445829, 371285683119367152, 371285685306790882, 371285685307350024, 371285684269203404, 371285684149324292, 371285686403481398, 371285686404049828, 371285686280938805, 371285686147500369]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362509257521521169, 362509261904548060⟩, ⟨(-428372616112892663), (-428318749273592993)⟩, true⟩

def words06 : List Nat := [371285686676971378, 371285686677592278, 371285687304417588, 371285688768497145, 371285689476383944, 371285689476943545, 371285686866315779, 371285686585336965, 371285689050403654, 371285690348262023]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495771331820491, 362495775719951413⟩, ⟨(-183096841363240073), (-183042881758315837)⟩, true⟩

def words07 : List Nat := [371285691679775602, 371285693011336236, 371285696251125104, 371285698326245888, 371285701292808548, 371285704259265816, 371285707289849914, 371285707290409760, 371285707353926462, 371285707908403186]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468328102663197, 362468332495777834⟩, ⟨316020453201069564, 316074503436280100⟩, true⟩

def words08 : List Nat := [371285711486558985, 371285711487118778, 371285711037894662, 371285709878320821, 371285708718656153, 371285708476881534, 371285707749835036, 371285708358627644, 371285708773560474, 371285708774141566]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362551287098501811, 362551291496694679⟩, ⟨(-1193444283760364979), (-1193390141126913651)⟩, true⟩

def words09 : List Nat := [371285709883927057, 371285711948994410, 371285714806582149, 371285714970771630, 371285714971205231, 371285714647981773, 371285716419883472, 371285717005796634, 371285720609171343, 371285724212417612]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk181
