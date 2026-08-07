import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk591

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583752108708410, 360583774318976200⟩, ⟨(-105629530444586766), (-104742733775799568)⟩, true⟩

def state01 : KState := ⟨⟨360578258602027480, 360578280820079698⟩, ⟨218976482234910085, 219863739002736999⟩, true⟩

def words00 : List Nat := [360582002074765916, 360582002075592549, 360582001946972008, 360582001606673783, 360582001266252179, 360582000852603752, 360582000595014901, 360582000609905237, 360582000610644612, 360582000389340445]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360619141758826086, 360619163984670177⟩, ⟨(-2197900853684048602), (-2197013136299320634)⟩, true⟩

def words01 : List Nat := [360582000348255840, 360582000370343473, 360582000678463866, 360582000944584694, 360582000945359513, 360582000934577480, 360582001084051700, 360582001427347824, 360582002056610988, 360582002686040261]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360629493816958296, 360629516050690820⟩, ⟨(-2810002755886037352), (-2809114572100507010)⟩, true⟩

def words02 : List Nat := [360582003172200688, 360582003768274855, 360582004650348012, 360582005532638241, 360582006198865585, 360582006913237999, 360582007483435674, 360582008053706242, 360582008615744051, 360582009420123089]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586231635396249, 360586253876907206⟩, ⟨(-251621902126094731), (-250733258361057767)⟩, true⟩

def words03 : List Nat := [360582010377323663, 360582011334649776, 360582012109313220, 360582012599012322, 360582013015260518, 360582013431735807, 360582013932091094, 360582014147576485, 360582014220009144, 360582014292551834]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598438802356431, 360598461051680684⟩, ⟨(-973652926189310795), (-972763820307778709)⟩, true⟩

def words04 : List Nat := [360582014650897322, 360582015151589013, 360582015501710948, 360582015851965799, 360582015960504036, 360582015961330587, 360582015784841223, 360582015541482604, 360582015339557335, 360582015618462180]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360608321968812358, 360608344226001237⟩, ⟨(-1558325741763334769), (-1557436170649916357)⟩, true⟩

def words05 : List Nat := [360582015753238546, 360582015888100771, 360582016242611881, 360582016739368219, 360582017162649267, 360582017586052262, 360582017788227392, 360582017948238795, 360582018393908273, 360582018839840593]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606981198961599, 360607003463933559⟩, ⟨(-1479061909382077183), (-1478171877782922311)⟩, true⟩

def words06 : List Nat := [360582019486435770, 360582019848398453, 360582019973764527, 360582020099226985, 360582020151374737, 360582020377994786, 360582020890090007, 360582021402326776, 360582021683834947, 360582022106887322]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599319661387984, 360599341934176945⟩, ⟨(-1025745811259067994), (-1024855317089601740)⟩, true⟩

def words07 : List Nat := [360582022469469382, 360582022832270211, 360582023387305639, 360582023657792099, 360582023682101443, 360582023706470512, 360582023762647542, 360582024044254268, 360582024337554990, 360582024631037600]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573160024147063, 360573182304801370⟩, ⟨522438228636617364, 523329188316627486⟩, true⟩

def words08 : List Nat := [360582024780611971, 360582024781439060, 360582024942967995, 360582025167108105, 360582025167813681, 360582025157787773, 360582024940743567, 360582024576978305, 360582024213070572, 360582023818373201]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360544386343956401, 360544408632406384⟩, ⟨2225751454422157330, 2226642875568567246⟩, true⟩

def words09 : List Nat := [360582023669673797, 360582023563096889, 360582023456425383, 360582023207262590, 360582022862358065, 360582022444663323, 360582022026739877, 360582021894447595, 360582021477636652, 360582020843142340]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk591
