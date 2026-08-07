import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk330

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479921296401245, 362479936506679679⟩, ⟨156019915840331672, 156359168491279450⟩, true⟩

def state01 : KState := ⟨⟨362452185906831026, 362452201126587618⟩, ⟨1071499646725782793, 1071839212206112139⟩, true⟩

def words00 : List Nat := [371284675139669788, 371284675140736408, 371284674769925668, 371284674388810662, 371284674007334875, 371284673462962881, 371284672459758961, 371284672060797567, 371284671661487465, 371284671263279715]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484332428534384, 362484347657928806⟩, ⟨10231602696276988, 10571486370199084⟩, true⟩

def words01 : List Nat := [371284670280392651, 371284669770114251, 371284669663792271, 371284669664861240, 371284669138900316, 371284668522519702, 371284668091320614, 371284668092494938, 371284667820471048, 371284667811967880]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362500531197278425, 362500546436303730⟩, ⟨(-524785033441229453), (-524444831707190101)⟩, true⟩

def words02 : List Nat := [371284667803078101, 371284667792317437, 371284667522792007, 371284667846707969, 371284668444154566, 371284668445239901, 371284668289379477, 371284668088957909, 371284668601843135, 371284669083764988]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465289880909649, 362465305129559456⟩, ⟨639459335291511318, 639799854971672692⟩, true⟩

def words03 : List Nat := [371284669868667455, 371284670653962108, 371284671177591638, 371284671178658557, 371284670619035005, 371284670341320458, 371284670699056667, 371284670700123597, 371284670116823930, 371284669531949640]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487993461960607, 362488008720161281⟩, ⟨(-110745360959838294), (-110404525671542444)⟩, true⟩

def words04 : List Nat := [371284668946604208, 371284668776124800, 371284668343996781, 371284668541276673, 371284668584651488, 371284668585725040, 371284667974328787, 371284667741674383, 371284668188777913, 371284668290955764]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485555146969437, 362485570414881065⟩, ⟨(-30064346489094299), (-29723190204139455)⟩, true⟩

def words05 : List Nat := [371284668333221185, 371284668375832974, 371284669332141730, 371284669957066619, 371284670602380286, 371284671248072694, 371284671892055002, 371284671893122627, 371284671345503942, 371284671374011033]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362458800787682717, 362458816065112334⟩, ⟨854568134141765725, 854909605141504891⟩, true⟩

def words06 : List Nat := [371284671780250310, 371284671781318424, 371284671117248585, 371284670413973249, 371284669710324948, 371284669082987342, 371284668148274945, 371284667963867593, 371284667779101483, 371284667580236057]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497585725782532, 362497601012874303⟩, ⟨(-428161529011007651), (-427819738435977743)⟩, true⟩

def words07 : List Nat := [371284666930816305, 371284667063658544, 371284668109067784, 371284668182206529, 371284668183057358, 371284668030041168, 371284668019066254, 371284668020243606, 371284668129608364, 371284668521763516]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473405485862099, 362473420782609183⟩, ⟨371902246325919779, 372244356348281887⟩, true⟩

def words08 : List Nat := [371284668913109213, 371284668914199207, 371284669454588454, 371284670181951752, 371284671081714479, 371284671082783426, 371284670893732258, 371284670618698516, 371284670343237553, 371284670234296953]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463052308231652, 362463067614594402⟩, ⟨714681304903849966, 715023733158214460⟩, true⟩

def words09 : List Nat := [371284670467473509, 371284671040994759, 371284671613726842, 371284671614795950, 371284670971223235, 371284670607785735, 371284670518286789, 371284670519363512, 371284670191521404, 371284669540067460]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk330
