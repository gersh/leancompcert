import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk102

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493513709451465, 362493515021610444⟩, ⟨(-94310225939189840), (-94301164416266484)⟩, true⟩

def state01 : KState := ⟨⟨362433768141058940, 362433769455881084⟩, ⟨515560537315494681, 515569626016440951⟩, true⟩

def words00 : List Nat := [371284280021519210, 371284280021817816, 371284276538621924, 371284272798349753, 371284269058700920, 371284266933139634, 371284263105086471, 371284264901870508, 371284265990931095, 371284265991240187]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491270035088113, 362491271352612909⟩, ⟨(-71684770168142057), (-71675653859263983)⟩, true⟩

def words01 : List Nat := [371284265698216750, 371284270349740558, 371284278855248324, 371284278855547342, 371284274600557439, 371284268284570126, 371284261969696665, 371284261431362331, 371284258078902783, 371284258765404294]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362441026748063355, 362441028068288914⟩, ⟨441846788826195928, 441855932750742300⟩, true⟩

def words02 : List Nat := [371284259361874778, 371284259362174778, 371284250983346434, 371284251579119397, 371284254939669464, 371284254939968909, 371284245572949128, 371284234468226822, 371284223365557758, 371284220241578332]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362391184354713703, 362391185677641282⟩, ⟨952430615438007199, 952439787018134127⟩, true⟩

def words03 : List Nat := [371284217979169638, 371284219938196695, 371284221740081727, 371284221740387653, 371284217921692048, 371284214839514921, 371284215456323966, 371284215456624096, 371284206459312288, 371284197375592272]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362440379825150914, 362440381150770342⟩, ⟨448373335357366266, 448382534515640868⟩, true⟩

def words04 : List Nat := [371284188293515228, 371284179483604861, 371284165908165711, 371284161861517916, 371284157815568673, 371284152475541460, 371284136866296234, 371284130783067211, 371284125787972911, 371284125788284064]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471663007821804, 362471664336177946⟩, ⟨127553299227721980, 127562526451222720⟩, true⟩

def words05 : List Nat := [371284121521158605, 371284115385472494, 371284112628966083, 371284112629296770, 371284111313653998, 371284110667615253, 371284110021599245, 371284109263480918, 371284098542497555, 371284097330958767]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475786472323915, 362475787803363043⟩, ⟨85402724632804952, 85411979397853122⟩, true⟩

def words06 : List Nat := [371284102468168787, 371284102468474617, 371284101057633508, 371284097924004736, 371284094790869771, 371284094436466467, 371284095831629692, 371284101274950827, 371284104451482307, 371284104451795162]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362663640707947909, 362663642041712650⟩, ⟨(-1844582137226412625), (-1844572854455370825)⟩, true⟩

def words07 : List Nat := [371284112318596177, 371284120993588080, 371284139150765428, 371284149006766796, 371284157101836742, 371284165195426910, 371284180673721788, 371284191427833168, 371284208884324029, 371284226337553972]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362521858541814724, 362521859878302873⟩, ⟨(-386846690865926967), (-386837380084238637)⟩, true⟩

def words08 : List Nat := [371284242755246968, 371284248524282874, 371284256685796369, 371284264845869775, 371284271818541177, 371284271818842912, 371284268254368957, 371284264466674726, 371284266352192327, 371284270005590383]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362417787006417503, 362417788345619952⟩, ⟨684937022878149386, 684946361603498306⟩, true⟩

def words09 : List Nat := [371284280464252167, 371284290921000931, 371284301286050916, 371284301286352669, 371284299083717763, 371284298397399919, 371284300802632868, 371284300802935359, 371284294448944806, 371284287992377574]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk102
