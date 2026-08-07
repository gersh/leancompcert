import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk437

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362511914978932057, 362511942272736480⟩, ⟨(-1155065489661712718), (-1154259594186300040)⟩, true⟩

def state01 : KState := ⟨⟨362484694733040199, 362484722039880095⟩, ⟨34459419307932346, 35265884499878038⟩, true⟩

def words00 : List Nat := [371285530113893956, 371285530115337077, 371285529917247677, 371285529864895725, 371285529915418804, 371285529916869477, 371285529582273358, 371285529182854490, 371285528853252300, 371285528854899539]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478680378238460, 362478707698075729⟩, ⟨297502355470299810, 298309388845478738⟩, true⟩

def words01 : List Nat := [371285529342327886, 371285529848797813, 371285530360347257, 371285530404163581, 371285530473173126, 371285530542858420, 371285531135085775, 371285531136529531, 371285531031578278, 371285530877143558]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487795113488769, 362487822446266363⟩, ⟨(-100915839341448901), (-100108240148872467)⟩, true⟩

def words02 : List Nat := [371285531089179682, 371285531266004525, 371285531815064726, 371285532364676071, 371285532773832845, 371285532775276818, 371285532655042743, 371285532824549267, 371285533209918086, 371285533263760844]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498248933296896, 362498276279229195⟩, ⟨(-558092961120974009), (-557284786609390731)⟩, true⟩

def words03 : List Nat := [371285533314022411, 371285533364753799, 371285533858108785, 371285534111602230, 371285534521875634, 371285534932733421, 371285535303142053, 371285535304589518, 371285535427265544, 371285535720334580]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362464623630743631, 362464650989559467⟩, ⟨912839145912296851, 913647884016959143⟩, true⟩

def words04 : List Nat := [371285536270084125, 371285536271528630, 371285536124932007, 371285535874030888, 371285535622573791, 371285535479365620, 371285535117946197, 371285534869716487, 371285534621034233, 371285534369765569]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499314185841743, 362499341557729860⟩, ⟨(-605037308232002733), (-604227998149917201)⟩, true⟩

def words05 : List Nat := [371285533893422923, 371285533863474555, 371285534323423760, 371285534324868733, 371285534192577372, 371285533982431970, 371285533771742210, 371285533676676601, 371285533786477691, 371285534103646318]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468273151112679, 362468300536020600⟩, ⟨753445778743186887, 754255658640674501⟩, true⟩

def words06 : List Nat := [371285534384814538, 371285534386259603, 371285534016960660, 371285534064220844, 371285534267776040, 371285534269221459, 371285533856669876, 371285533450842236, 371285533044441625, 371285532787760164]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362452473150107480, 362452500548046280⟩, ⟨1445077910717018557, 1445888361039591019⟩, true⟩

def words07 : List Nat := [371285532395072537, 371285532070287658, 371285531745042231, 371285531419242604, 371285530489597875, 371285529580620751, 371285528670896399, 371285528283533187, 371285527531076674, 371285526778312146]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485698209583817, 362485725620437551⟩, ⟨(-9631100719716349), (-8820084914531599)⟩, true⟩

def words08 : List Nat := [371285526024942724, 371285525793945690, 371285525331801898, 371285525362695381, 371285525363844467, 371285525270493874, 371285524481562903, 371285524215028342, 371285524201151862, 371285524207249578]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480644930659677, 362480672354727144⟩, ⟨211736141392449597, 212547735891438651⟩, true⟩

def words09 : List Nat := [371285524208338216, 371285524114044161, 371285524444742598, 371285524609491999, 371285524897414076, 371285525185860868, 371285525476138880, 371285525477585629, 371285525151750099, 371285525042761196]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk437
