import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk023

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361326695459023540, 361326695483521968⟩, ⟨(-1809834370716271318), (-1809834332395603252)⟩, true⟩

def state01 : KState := ⟨⟨360639912202282397, 360639912227008680⟩, ⟨(-232526034742589371), (-232525995896707777)⟩, true⟩

def words00 : List Nat := [360540361612858193, 360540387228190451, 360540387228210181, 360540380243582808, 360540373265009501, 360540315124347074, 360540074491546016, 360539738594256700, 360539402987909049, 360539295179887647]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360300517320929100, 360300517345881320⟩, ⟨555600860229005528, 555600899597967658⟩, true⟩

def words01 : List Nat := [360539522493764402, 360539749611092460, 360539878051932942, 360539978066148200, 360540027902589306, 360540077696018591, 360540112636559278, 360540112636583376, 360540103762241928, 360540000492259755]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360268638055108727, 360268638080288586⟩, ⟨630083758747866746, 630083798646082808⟩, true⟩

def words02 : List Nat := [360539897311259868, 360539831711313056, 360539909319952747, 360539986861837240, 360539986861859480, 360539911592549983, 360539657401489324, 360539444167672725, 360539231116961212, 360539060311467163]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585927944968865, 360585927970379740⟩, ⟨(-112389704535597332), (-112389664097966886)⟩, true⟩

def words03 : List Nat := [360538944300236066, 360538671121167591, 360538398176281374, 360538305588957148, 360538305588977442, 360538258779021703, 360538212009123290, 360538036008936240, 360537898199369824, 360537918716173005]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581270430197092, 360581270455837243⟩, ⟨(-102657658653984900), (-102657617678683886)⟩, true⟩

def words04 : List Nat := [360538117808941193, 360538140632994417, 360538140633016230, 360538015991354564, 360537891455993530, 360537629591103290, 360537574223235804, 360537635563137628, 360537635563159609, 360537604944276765]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361314612110302432, 361314612136173972⟩, ⟨(-1829223708291952114), (-1829223666771727290)⟩, true⟩

def words05 : List Nat := [360537801111034017, 360537997111061132, 360538234018273198, 360538461637723479, 360538530750478961, 360538599804591799, 360538845605351931, 360539188792859299, 360539517362092793, 360539845653000856]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360915007868089157, 360915007894194996⟩, ⟨(-888131727099166800), (-888131685024809396)⟩, true⟩

def words06 : List Nat := [360540082084154304, 360540144948995050, 360540250417946534, 360540355797713506, 360540355797734304, 360540367844012611, 360540367844034784, 360540315764409577, 360540268786561616, 360540426837668295]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360441356530585719, 360441356556925062⟩, ⟨238004726395147429, 238004769024081071⟩, true⟩

def words07 : List Nat := [360540759214608464, 360541091311421019, 360541289236921169, 360541314892978706, 360541314892999535, 360541259167072175, 360541321681503982, 360541400595978942, 360541400596001141, 360541358560716693]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361002945596271861, 361002945622845519⟩, ⟨(-1099623004840580211), (-1099622961652777739)⟩, true⟩

def words08 : List Nat := [360541448088037095, 360541670852467369, 360542066778745067, 360542462373013798, 360542705831753261, 360542778913687858, 360542778913708515, 360542745779191511, 360542852333425324, 360543044760590071]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361497986317895293, 361497986344706839⟩, ⟨(-2285901282785100176), (-2285901239027559186)⟩, true⟩

def words09 : List Nat := [360543146811718787, 360543248777558968, 360543522858131410, 360543936167020553, 360544301813859498, 360544667155615422, 360544904725116545, 360545130471782905, 360545527495083611, 360545924187677452]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk023
