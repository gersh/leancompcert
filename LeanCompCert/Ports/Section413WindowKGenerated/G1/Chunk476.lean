import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk476

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492302229767049, 362492334838754364⟩, ⟨(-336331632736234039), (-335282938632964959)⟩, true⟩

def state01 : KState := ⟨⟨362479282034431530, 362479314657701184⟩, ⟨283406684818134321, 284456058834724917⟩, true⟩

def words00 : List Nat := [371285291324193156, 371285291325776350, 371285290834874696, 371285290745760248, 371285290701033427, 371285290702624258, 371285290327281724, 371285289861722311, 371285289395514084, 371285289370132076]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471815385237249, 362471848022752873⟩, ⟨639046094374455787, 640096146713476727⟩, true⟩

def words01 : List Nat := [371285289488983555, 371285289733943289, 371285289940942731, 371285289942557280, 371285289896363958, 371285289919490370, 371285290224979649, 371285290226564814, 371285290053512399, 371285289772998852]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490158063800441, 362490190715504888⟩, ⟨(-234530453596842691), (-233479725514110383)⟩, true⟩

def words02 : List Nat := [371285289491827431, 371285289395872592, 371285289199256729, 371285289322047042, 371285289370727401, 371285289372311366, 371285288833980362, 371285288666036385, 371285288767066251, 371285288871631904]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484033117103492, 362484065783238229⟩, ⟨57245019890328616, 58296435361613198⟩, true⟩

def words03 : List Nat := [371285288976874829, 371285289082675845, 371285289394488063, 371285289531145967, 371285289682115428, 371285289833650433, 371285289956216991, 371285289957801426, 371285289493669753, 371285289469958666]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362463387288549536, 362463419968819174⟩, ⟨1040971201941174128, 1042023290873023046⟩, true⟩

def words04 : List Nat := [371285289563226359, 371285289564839270, 371285289382553754, 371285289202042133, 371285289020951484, 371285288920602938, 371285288601386342, 371285288512444622, 371285288422971309, 371285288243548934]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501319705558559, 362501352400140445⟩, ⟨(-766736291130136379), (-765683520148361539)⟩, true⟩

def words05 : List Nat := [371285287785701839, 371285287611905255, 371285287700899537, 371285287702484430, 371285287381093358, 371285286982792268, 371285286622994752, 371285286624749745, 371285286860814851, 371285287199658954]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468827980957582, 362468860689856364⟩, ⟨781876579379677866, 782930032778319466⟩, true⟩

def words06 : List Nat := [371285287539146484, 371285287540731498, 371285287294080673, 371285287096785687, 371285286898678162, 371285286836734288, 371285286188451470, 371285285542031213, 371285284895004381, 371285284646910661]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362449964079363575, 362449996802543826⟩, ⟨1681292918729794624, 1682347052998193618⟩, true⟩

def words07 : List Nat := [371285284303467200, 371285284164882216, 371285284025765625, 371285283885515457, 371285283365195685, 371285282977915946, 371285282589866987, 371285282374484170, 371285281665208656, 371285280926977513]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469090004624540, 362469122742001538⟩, ⟨769322094715132518, 770376905956580092⟩, true⟩

def words08 : List Nat := [371285280188050042, 371285279888625813, 371285279368933482, 371285279185022940, 371285279000615532, 371285278636955497, 371285277749476345, 371285277232226720, 371285276714164757, 371285276587796392]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480426578474182, 362480459330317347⟩, ⟨228598409188750876, 229653910394671402⟩, true⟩

def words09 : List Nat := [371285276250295467, 371285275828444732, 371285275405982533, 371285275324186526, 371285275021314186, 371285274854669294, 371285274687470336, 371285274514975017, 371285273976674431, 371285273877705076]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk476
