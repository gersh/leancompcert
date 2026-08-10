import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk591A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk591A
