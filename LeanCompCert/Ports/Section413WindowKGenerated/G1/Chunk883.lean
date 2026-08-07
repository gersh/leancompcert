import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk883

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470103122248974, 362470220930037507⟩, ⟨1314888999840609942, 1321912666615966748⟩, true⟩

def state01 : KState := ⟨⟨362479760978148373, 362479878813457222⟩, ⟨462096848813105489, 469122945774438567⟩, true⟩

def words00 : List Nat := [371285191460958046, 371285191422911335, 371285191327741515, 371285191339383956, 371285191341808327, 371285191317592036, 371285191139163748, 371285191079210187, 371285191039303333, 371285191042488753]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470474620896200, 362470592484302516⟩, ⟨1282277374158461412, 1289305952542586968⟩, true⟩

def words01 : List Nat := [371285190984634676, 371285190927986072, 371285190918614166, 371285190922006737, 371285190919011208, 371285190925527187, 371285190929546635, 371285190932623809, 371285190765658706, 371285190604236196]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479143546310978, 362479261437120299⟩, ⟨516610051106387984, 523641049865410188⟩, true⟩

def words02 : List Nat := [371285190441037938, 371285190406884099, 371285190273212850, 371285190131399581, 371285189988440028, 371285189885159494, 371285189735357853, 371285189714860572, 371285189693295740, 371285189672712572]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495614970629454, 362495732889245102⟩, ⟨(-938416058592951309), (-931382603557440227)⟩, true⟩

def words03 : List Nat := [371285189634982321, 371285189665934115, 371285189748653609, 371285189751734112, 371285189695584942, 371285189626375083, 371285189611273379, 371285189614665405, 371285189727463521, 371285189850298776]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478126723782582, 362478244670160535⟩, ⟨606540901185831262, 613576808882493608⟩, true⟩

def words04 : List Nat := [371285189946801401, 371285189949879420, 371285189882682181, 371285189893672663, 371285189942255440, 371285189945333629, 371285189837022915, 371285189702117908, 371285189565980100, 371285189512366336]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474881737054965, 362474999711151818⟩, ⟨893304794259656125, 900343151063034683⟩, true⟩

def words05 : List Nat := [371285189468154675, 371285189503867097, 371285189538916079, 371285189542048094, 371285189470368007, 371285189418778906, 371285189420888724, 371285189423967194, 371285189310885080, 371285189199054297]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475251495759103, 362475369497465604⟩, ⟨860621789141857000, 867662585675083588⟩, true⟩

def words06 : List Nat := [371285189085871762, 371285189004134443, 371285188856927177, 371285188750657938, 371285188643460943, 371285188513891517, 371285188285097431, 371285188165090441, 371285188043386569, 371285188017163184]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477817004396804, 362477935034120047⟩, ⟨633910351027787136, 640953623543535722⟩, true⟩

def words07 : List Nat := [371285187908382677, 371285187801825871, 371285187694045813, 371285187696755793, 371285187666631989, 371285187635779572, 371285187603860113, 371285187567579149, 371285187359743405, 371285187281501169]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470204934327956, 362470322991516232⟩, ⟨1306749445861545088, 1313795145880079434⟩, true⟩

def words08 : List Nat := [371285187228107153, 371285187231241220, 371285187167220717, 371285187088987194, 371285187009545731, 371285186937477508, 371285186800154840, 371285186746694949, 371285186692282611, 371285186608960288]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489513757521566, 362489631842606032⟩, ⟨(-400059900088701612), (-393011734193609090)⟩, true⟩

def words09 : List Nat := [371285186442890986, 371285186392159953, 371285186385665984, 371285186388745971, 371285186277854382, 371285186149559143, 371285186019957270, 371285186019508142, 371285186004975889, 371285186058800492]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk883
