import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk424

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362461087195840857, 362461112826916660⟩, ⟨1019226524186475807, 1019960833188697213⟩, true⟩

def state01 : KState := ⟨⟨362506311840077935, 362506337483654668⟩, ⟨(-898477468562260177), (-897742629457660663)⟩, true⟩

def words00 : List Nat := [371285167940555124, 371285167879548263, 371285167804760109, 371285168046718718, 371285168112976526, 371285168114404520, 371285168149571594, 371285168446650482, 371285169299481435, 371285169800047641]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490000791081000, 362490026447391269⟩, ⟨(-206623133718679453), (-205887754520417057)⟩, true⟩

def words01 : List Nat := [371285170254946768, 371285170710285053, 371285171361169852, 371285171735669329, 371285172161315000, 371285172587500692, 371285173012566994, 371285173013964610, 371285172891792789, 371285173007950417]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362456134399716100, 362456160068454626⟩, ⟨1230230879841947997, 1230966786313023719⟩, true⟩

def words02 : List Nat := [371285173572855110, 371285173574252904, 371285173398590935, 371285173222941181, 371285173046754022, 371285173043713717, 371285172763610315, 371285172435476210, 371285172106898750, 371285171776828726]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362505243854905471, 362505269536299628⟩, ⟨(-853701660539594785), (-852965217028685951)⟩, true⟩

def words03 : List Nat := [371285171094039059, 371285170904226200, 371285171078117407, 371285171079540090, 371285170991296031, 371285170743530635, 371285170801847686, 371285170916527292, 371285171391054693, 371285171866192216]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471400153214732, 362471425847245334⟩, ⟨582758805764395286, 583495785630516992⟩, true⟩

def words04 : List Nat := [371285172210795580, 371285172212193937, 371285171976038511, 371285172137010080, 371285172410912350, 371285172412313797, 371285172116479320, 371285171819348101, 371285171521627281, 371285171331005771]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470349416100611, 362470375122696754⟩, ⟨627432636921374827, 628170150259247725⟩, true⟩

def words05 : List Nat := [371285171239929194, 371285171473193606, 371285171684741618, 371285171686140237, 371285171158057849, 371285170658381317, 371285170212097689, 371285170213505286, 371285169867831559, 371285169520960043]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362502026076786313, 362502051795911790⟩, ⟨(-717601577477224593), (-716863532078871915)⟩, true⟩

def words06 : List Nat := [371285169380388673, 371285169384642938, 371285169943547421, 371285170503013426, 371285170976146412, 371285170977549293, 371285171347410632, 371285171811107805, 371285172502442619, 371285172901323039]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362510033782947853, 362510059514845715⟩, ⟨(-1057709311703673631), (-1056970723799478637)⟩, true⟩

def words07 : List Nat := [371285173205057242, 371285173509238430, 371285174367862693, 371285174950805385, 371285175706424072, 371285176462556096, 371285177216421449, 371285177318012987, 371285177904701935, 371285178492181478]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362506885082452130, 362506910826833899⟩, ⟨(-923934165044967123), (-923195046760103563)⟩, true⟩

def words08 : List Nat := [371285179471856205, 371285179956350486, 371285180278307829, 371285180600699206, 371285181038850411, 371285181232786864, 371285181980804371, 371285182729368376, 371285183476648064, 371285183989462218]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362525739797166654, 362525765554182937⟩, ⟨(-1725150252605198555), (-1724410597415655113)⟩, true⟩

def words09 : List Nat := [371285185056319697, 371285186123836089, 371285187474843061, 371285188088010490, 371285188619821207, 371285189152062661, 371285189828069990, 371285190229955745, 371285191185619538, 371285192141853447]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk424
