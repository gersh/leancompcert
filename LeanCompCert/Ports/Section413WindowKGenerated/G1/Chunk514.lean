import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk514

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362457284724211178, 362457322984313935⟩, ⟨1421246063185712740, 1422574635290889708⟩, true⟩

def state01 : KState := ⟨⟨362462488568407226, 362462526843934176⟩, ⟨1153744759891609729, 1155074124873752867⟩, true⟩

def words00 : List Nat := [371284998996382242, 371284998615704196, 371284998092099041, 371284997764235126, 371284997435867185, 371284997006568654, 371284996072848982, 371284995517825285, 371284994961847522, 371284994731988519]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474419638845898, 362474457930001762⟩, ⟨540332866120501329, 541663034666117497⟩, true⟩

def words01 : List Nat := [371284994296249609, 371284993861771485, 371284993426627608, 371284993369822751, 371284993218409778, 371284993086116756, 371284992953247546, 371284992806459051, 371284992225226768, 371284992022469015]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471085611332829, 362471123917839813⟩, ⟨711843847628573450, 713174805607420578⟩, true⟩

def words02 : List Nat := [371284991991419723, 371284991993169689, 371284991853203922, 371284991691902654, 371284991529939122, 371284991321242679, 371284990923361468, 371284990903631738, 371284990883350169, 371284990820534883]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362504769378708312, 362504807700775598⟩, ⟨(-1020688443278420093), (-1019356684953392573)⟩, true⟩

def words03 : List Nat := [371284990659849798, 371284990769687169, 371284991156913836, 371284991158634440, 371284991042657542, 371284990864134643, 371284990881768499, 371284990891630650, 371284991278039737, 371284991665221208]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490387494355098, 362490425831965350⟩, ⟨(-280882134153318559), (-279549576218981689)⟩, true⟩

def words04 : List Nat := [371284992045692908, 371284992066294836, 371284992243029963, 371284992420628532, 371284992714067402, 371284992715789841, 371284992599889034, 371284992410964200, 371284992407687595, 371284992515290864]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362476176241607333, 362476214594696105⟩, ⟨450439732718263462, 451773087100604424⟩, true⟩

def words05 : List Nat := [371284992888954455, 371284993263289263, 371284993635769949, 371284993647411458, 371284993709866435, 371284993773193654, 371284993992286175, 371284993994019029, 371284993875062654, 371284993706377034]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480523200447373, 362480561568932995⟩, ⟨226835055895555575, 228169202680150071⟩, true⟩

def words06 : List Nat := [371284993743357424, 371284993764372772, 371284994104646260, 371284994445653170, 371284994742963578, 371284994744685155, 371284994539069859, 371284994502052290, 371284994619466428, 371284994621248522]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494013577210235, 362494051961450624⟩, ⟨(-467598159528000454), (-466263201771013778)⟩, true⟩

def words07 : List Nat := [371284994536446889, 371284994371283708, 371284994415178883, 371284994468479280, 371284994581724245, 371284994695609915, 371284994809447036, 371284994811198931, 371284994787506931, 371284994965631371]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488559049170900, 362488597448720731⟩, ⟨(-186756477230805004), (-185420731262047162)⟩, true⟩

def words08 : List Nat := [371284995519442325, 371284995571320086, 371284995617655891, 371284995664555018, 371284995725141031, 371284995727038534, 371284995846647404, 371284996096078605, 371284996345142313, 371284996416865416]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486225625751754, 362486264040872155⟩, ⟨(-66609930476701484), (-65273382699824068)⟩, true⟩

def words09 : List Nat := [371284996630103548, 371284996844232423, 371284997201510504, 371284997203233138, 371284997058388105, 371284996850225190, 371284996698152708, 371284996700068372, 371284996594627258, 371284996621157979]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk514
