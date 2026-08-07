import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk400

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566362327230767, 360566372182649880⟩, ⟨649972773397480568, 650239215711725324⟩, true⟩

def state01 : KState := ⟨⟨360589147139610200, 360589157000140359⟩, ⟨(-261591705784993465), (-261325059003641075)⟩, true⟩

def words00 : List Nat := [360582627757094746, 360582627222672327, 360582627391840329, 360582627721333483, 360582627721846448, 360582627453977280, 360582626739544200, 360582626120760879, 360582625505977747, 360582625669781117]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604321047044219, 360604330912745795⟩, ⟨(-868759097841375776), (-868492244127733836)⟩, true⟩

def words01 : List Nat := [360582625670263961, 360582625521797686, 360582625847552596, 360582626755392135, 360582627392683312, 360582628030031242, 360582628355180802, 360582628914026156, 360582629456750917, 360582629999621992]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589299546613699, 360589309417417715⟩, ⟨(-267553245847648670), (-267286187907831676)⟩, true⟩

def words02 : List Nat := [360582630913939477, 360582631206783289, 360582631207270750, 360582631185708477, 360582631164059436, 360582631286354944, 360582631773892543, 360582632261507522, 360582632270018940, 360582632437379549]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360626727281392917, 360626737157324024⟩, ⟨(-1766097292081670506), (-1765830028879222282)⟩, true⟩

def words03 : List Nat := [360582633227346331, 360582634017438018, 360582634512888271, 360582634671124584, 360582634671625936, 360582634215825887, 360582633926211486, 360582634405767713, 360582635507673617, 360582636609663396]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585091417708083, 360585101298801271⟩, ⟨(-98989097978248104), (-98721628060537306)⟩, true⟩

def words04 : List Nat := [360582637393077433, 360582637555651950, 360582638008826354, 360582638462136656, 360582638756988831, 360582638757531286, 360582638431613387, 360582637624253467, 360582636816830465, 360582636400844653]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360542084105632925, 360542093991833432⟩, ⟨1623740910901651218, 1624008585393337982⟩, true⟩

def words05 : List Nat := [360582636518600312, 360582636636453952, 360582636636939590, 360582636341918429, 360582636061258257, 360582635622706516, 360582635184018001, 360582635106644308, 360582634408790873, 360582633397359976]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595523779466687, 360595533670798403⟩, ⟨(-517355421721784552), (-517087541649038426)⟩, true⟩

def words06 : List Nat := [360582632385864528, 360582631157290548, 360582630409154113, 360582630282881702, 360582630156573297, 360582629497716016, 360582628988623225, 360582628944873782, 360582629064755031, 360582629387360280]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360554764797896413, 360554774694392418⟩, ⟨1116049194597835042, 1116317281629311082⟩, true⟩

def words07 : List Nat := [360582629387845062, 360582629261333018, 360582629134726377, 360582629383437431, 360582629383900109, 360582629213962920, 360582629043979390, 360582628493553167, 360582627616292354, 360582626921977980]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589647559659969, 360589657461275477⟩, ⟨(-282225883216981940), (-281957590970693750)⟩, true⟩

def words08 : List Nat := [360582626227518429, 360582625995172123, 360582625802912426, 360582625255925642, 360582624708874045, 360582624004421349, 360582624115889216, 360582624482373505, 360582624482866317, 360582624521439337]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360641197682450962, 360641207589190408⟩, ⟨(-2349222890981464164), (-2348954393291447982)⟩, true⟩

def words09 : List Nat := [360582625108817447, 360582625696327996, 360582626904320675, 360582627492991928, 360582627493501173, 360582627469928821, 360582627870104600, 360582628711077002, 360582630172336073, 360582631633645872]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk400
