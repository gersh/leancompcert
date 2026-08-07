import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk242

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362553658444920890, 362553666414671869⟩, ⟨(-1655085916856505095), (-1654955511833931935)⟩, true⟩

def state01 : KState := ⟨⟨362552263993831853, 362552271970463137⟩, ⟨(-1621478034110668073), (-1621347462549568215)⟩, true⟩

def words00 : List Nat := [371285285473301467, 371285286021158539, 371285288280622181, 371285290540283898, 371285293151625913, 371285294987282585, 371285296812138224, 371285298637111334, 371285301814173194, 371285304581154577]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487395844044783, 362487403827539992⟩, ⟨(-50592278497104741), (-50461540724825105)⟩, true⟩

def words01 : List Nat := [371285307997124125, 371285311413109451, 371285314515308271, 371285315343188467, 371285316447859649, 371285317552820831, 371285320050284385, 371285320274309749, 371285320360916028, 371285320447798247]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362517794937406329, 362517802927726287⟩, ⟨(-786845190244226726), (-786714287141190506)⟩, true⟩

def words02 : List Nat := [371285321973671010, 371285322898799033, 371285325532405888, 371285328166114777, 371285330461782322, 371285330485451826, 371285331195058632, 371285331904991368, 371285334322432302, 371285335663183298]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362513916006222953, 362513924003500331⟩, ⟨(-692822174471944853), (-692691102755355575)⟩, true⟩

def words03 : List Nat := [371285336917343626, 371285338171667090, 371285340276223759, 371285341755710442, 371285343498678024, 371285345241785746, 371285346984500362, 371285346985263724, 371285347636920654, 371285348816719450]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362501005559164528, 362501013563257384⟩, ⟨(-379754322689313059), (-379623085730792809)⟩, true⟩

def words04 : List Nat := [371285350682541919, 371285351332056433, 371285351970865263, 371285352609878939, 371285353564558708, 371285353682244128, 371285355505103257, 371285357328142297, 371285359002229717, 371285359648543319]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362560599443813742, 362560607454799745⟩, ⟨(-1825140600572769990), (-1825009196420539642)⟩, true⟩

def words05 : List Nat := [371285361999725690, 371285364351100387, 371285368176265423, 371285370032910007, 371285371260838314, 371285372488893005, 371285375197258981, 371285377262719440, 371285380364237140, 371285383465828947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362529888893800692, 362529896911686128⟩, ⟨(-1079968457087582122), (-1079836885518894258)⟩, true⟩

def words06 : List Nat := [371285386556661234, 371285388249582509, 371285391165810878, 371285394082207018, 371285397187969867, 371285398789753939, 371285400381298960, 371285401972962845, 371285404249689197, 371285406083721937]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491815610081431, 362491823634859660⟩, ⟨(-155580273002664196), (-155448534111075328)⟩, true⟩

def words07 : List Nat := [371285409024752978, 371285411965859545, 371285414828437239, 371285415721648559, 371285417120823697, 371285418520268792, 371285420767715733, 371285421041301029, 371285421305571579, 371285421570113107]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362524393596298280, 362524401627938056⟩, ⟨(-946644281892114701), (-946512376368029593)⟩, true⟩

def words08 : List Nat := [371285423534604714, 371285424887733672, 371285426926188851, 371285428964773878, 371285430758114527, 371285430758879522, 371285431210704062, 371285432130689250, 371285434464663868, 371285436069650294]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362495024823140438, 362495032861743110⟩, ⟨(-232989557123596585), (-232857482435425977)⟩, true⟩

def words09 : List Nat := [371285437676766059, 371285439283994442, 371285441927526375, 371285443730448690, 371285445973005933, 371285448215676804, 371285450163529784, 371285450164295245, 371285450248348665, 371285450643627172]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk242
