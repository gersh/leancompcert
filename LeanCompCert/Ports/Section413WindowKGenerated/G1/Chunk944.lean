import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk944

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492946288554657, 362493081632291846⟩, ⟨(-755425158869361681), (-746798938540420827)⟩, true⟩

def state01 : KState := ⟨⟨362488757360786598, 362488892734398092⟩, ⟨(-359971813685526003), (-351342773064832811)⟩, true⟩

def words00 : List Nat := [371285170782149378, 371285170792119687, 371285170894862552, 371285170999282692, 371285171130412272, 371285171155160918, 371285171178743524, 371285171203472746, 371285171273402559, 371285171316628290]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480396698230681, 362480532101591790⟩, ⟨429424149480303123, 438055998915579003⟩, true⟩

def words01 : List Nat := [371285171440517635, 371285171565716283, 371285171669844826, 371285171673151736, 371285171627576875, 371285171596362810, 371285171630076686, 371285171633392763, 371285171587829025, 371285171542376747]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490498328822562, 362490633761812508⟩, ⟨(-524424943817348753), (-515790296680142623)⟩, true⟩

def words02 : List Nat := [371285171558585607, 371285171569418782, 371285171598511978, 371285171628969166, 371285171639866458, 371285171643176259, 371285171527060617, 371285171524894535, 371285171613910182, 371285171675244749]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490595495117865, 362490730958248228⟩, ⟨(-533591675841774541), (-524954182389786219)⟩, true⟩

def words03 : List Nat := [371285171735236785, 371285171796409662, 371285171968382999, 371285172085853553, 371285172178635276, 371285172272630560, 371285172343065768, 371285172346378403, 371285172354136311, 371285172417123190]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489230273507003, 362489365766107703⟩, ⟨(-404639292712169380), (-395999015928410570)⟩, true⟩

def words04 : List Nat := [371285172590422255, 371285172615329900, 371285172639083152, 371285172663986079, 371285172708358217, 371285172718056704, 371285172838474518, 371285172960280540, 371285173078550493, 371285173126369337]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496452985848577, 362496588508340669⟩, ⟨(-1086882877845737396), (-1078239777666327766)⟩, true⟩

def words05 : List Nat := [371285173209249900, 371285173293780528, 371285173459348211, 371285173490014746, 371285173501495956, 371285173514013253, 371285173572763170, 371285173605178390, 371285173728265826, 371285173852793234]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485122577680245, 362485258130016425⟩, ⟨(-16586357657001656), (-7940438259883134)⟩, true⟩

def words06 : List Nat := [371285173959346281, 371285173962655447, 371285174018597348, 371285174105572215, 371285174196567706, 371285174199876681, 371285174151333404, 371285174103585530, 371285174073754174, 371285174078421122]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473920034488468, 362474055616673894⟩, ⟨1041813262434440488, 1050462001843653882⟩, true⟩

def words07 : List Nat := [371285174144122840, 371285174211253042, 371285174276247654, 371285174279556997, 371285174195023194, 371285174146389372, 371285174155642650, 371285174158952340, 371285174083701420, 371285173969784009]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494155136112724, 362494290747930551⟩, ⟨(-870080174516877284), (-861428635290944666)⟩, true⟩

def words08 : List Nat := [371285173854349764, 371285173841164994, 371285173834608221, 371285173889846713, 371285173926801145, 371285173930177987, 371285173940952542, 371285173990240835, 371285174132825374, 371285174232756715]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493330032113822, 362493465674110134⟩, ⟨(-792110775527642464), (-783456384589581748)⟩, true⟩

def words09 : List Nat := [371285174332108172, 371285174432523092, 371285174578107403, 371285174669217192, 371285174792827674, 371285174917751287, 371285175041416919, 371285175044729000, 371285175126175152, 371285175218087557]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk944
