import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk159

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360533537619174188, 360533539056249800⟩, ⟨753017981126059958, 753033451368438600⟩, true⟩

def state01 : KState := ⟨⟨360593938036758222, 360593939475715239⟩, ⟨(-207894911463441485), (-207879411297131293)⟩, true⟩

def words00 : List Nat := [360580897643182918, 360580897643382833, 360580894683225571, 360580889262908947, 360580883843238013, 360580877388025455, 360580874478873130, 360580874997570655, 360580874997748817, 360580874337678841]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360680992743212844, 360680994184060865⟩, ⟨(-1593708431097161635), (-1593692900835597499)⟩, true⟩

def words01 : List Nat := [360580875020732143, 360580875703758631, 360580880329361161, 360580882423272862, 360580882423457207, 360580881179582026, 360580879935825803, 360580881557218101, 360580887845861655, 360580894133760282]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360607395390829541, 360607396833584543⟩, ⟨(-422029212015097121), (-422013651385196957)⟩, true⟩

def words02 : List Nat := [360580897714536454, 360580899781300697, 360580905786386463, 360580911790776348, 360580914533798196, 360580914533998376, 360580913356296468, 360580910184242112, 360580907012546983, 360580906741852374]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360552035746899801, 360552037191542673⟩, ⟨460354458394621185, 460370049107790949⟩, true⟩

def words03 : List Nat := [360580911093551495, 360580915444745936, 360580917573120082, 360580917603698301, 360580917603865981, 360580916602900692, 360580918531890845, 360580920436593380, 360580920436777954, 360580918624987328]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360750407021447244, 360750408467981142⟩, ⟨(-2702872377332657264), (-2702856756467222152)⟩, true⟩

def words04 : List Nat := [360580916813379307, 360580918440415121, 360580922935367343, 360580927429793986, 360580928603448712, 360580931925053880, 360580937345467432, 360580942765261580, 360580950363918272, 360580960987793868]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360698404612080230, 360698406060524929⟩, ⟨(-1873424871161683832), (-1873409219809538294)⟩, true⟩

def words05 : List Nat := [360580969115781277, 360580977242770786, 360580983950777587, 360580992659508428, 360581000339287715, 360581008018137139, 360581013738277099, 360581017174873325, 360581024530229026, 360581031884733341]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360621753639984901, 360621755090318749⟩, ⟨(-649803864206813891), (-649788182694137917)⟩, true⟩

def words06 : List Nat := [360581039757676146, 360581046056638327, 360581049605310864, 360581053153561226, 360581054832486890, 360581058483943286, 360581061998172303, 360581065511996735, 360581067038596074, 360581069586424558]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360755235351931370, 360755236804160681⟩, ⟨(-2781948986913645687), (-2781933275121023093)⟩, true⟩

def words07 : List Nat := [360581076047213229, 360581082507252848, 360581092879258977, 360581103716514878, 360581111114523089, 360581118511619105, 360581126994305085, 360581137468716927, 360581148363706959, 360581159257378814]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360643154186123910, 360643155640268969⟩, ⟨(-990925588838631838), (-990909846422947418)⟩, true⟩

def words08 : List Nat := [360581167147269790, 360581172738704587, 360581178852065087, 360581184964720430, 360581188866628023, 360581188883016353, 360581188883195459, 360581186806037143, 360581185043014487, 360581188918586589]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587060556190068, 360587062012227085⟩, ⟨(-93368023380616466), (-93352250702760092)⟩, true⟩

def words09 : List Nat := [360581196697455084, 360581204475389168, 360581210305776542, 360581215634219490, 360581218275163038, 360581220915826807, 360581224785805124, 360581227131490620, 360581227496349850, 360581227861192603]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk159
