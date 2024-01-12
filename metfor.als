open util/ boolean
module CinemaBookingSystem

// Signatures
abstract sig User {
    username: lone Username,
    password: lone Password
}

sig Username {}
sig Password {}
sig DateTime {}

abstract sig Film {
    title: lone Title,
    duration: lone Int,
    genre: lone Genre
}

sig Title {}
sig Genre {}

abstract sig Location {
    name: lone Name,
    address: lone Address
}

sig Name {}
sig Address {}

abstract sig Showtime {
    time: lone DateTime
}

abstract sig Seat {
    seatNumber: lone SeatNumber,
    isOccupied: lone Int
}

sig SeatNumber {}

sig Login {
    username: one Username,
    password: one Password
}

sig PilihFilm {
    availableFilms: set Film
}

sig PilihLokasi {
    availableLocations: set Location
}

sig PilihJamTayang {
    availableShowtimes: set Showtime
}

sig PilihKursi {
    availableSeats: set Seat
}

sig ProsesPembayaran {
    paymentDetails: lone String
}

// Facts
fact UserUnique {
    all u1, u2: User | u1 != u2 implies u1.username != u2.username
}

fact FilmUnique {
    all f1, f2: Film | f1 != f2 implies f1.title != f2.title
}

fact LocationUnique {
    all l1, l2: Location | l1 != l2 implies l1.name != l2.name
}

fact ShowtimeUnique {
    all st1, st2: Showtime | st1 != st2 implies st1.time != st2.time
}

fact SeatUnique {
    all s1, s2: Seat | s1 != s2 implies s1.seatNumber != s2.seatNumber
}

// Predicates
pred VerifyLogin(l: Login, u: User) {
    l.username = u.username and l.password = u.password
}

pred KursiAvailable(k: PilihKursi, s: Seat) {
    s in k.availableSeats
}

pred JamTayangAvailable(j: PilihJamTayang, st: Showtime) {
    st in j.availableShowtimes
}

// Assertions
assert FilmSelectionValid {
    all pf: PilihFilm, f: Film | f in pf.availableFilms
}

assert LokasiSelectionValid {
    all pl: PilihLokasi, l: Location | l in pl.availableLocations
}

assert PembayaranValid {
    all pp: ProsesPembayaran, s: lone String | s = pp.paymentDetails
}

assert KursiBookingValid {
    all pk: PilihKursi, s: Seat | s in pk.availableSeats implies s.isOccupied = 0
}

run {} for 5 but exactly 3 User, 5 Film, 3 Location, 5 Showtime, 20 Seat, 2 Login, 3 PilihFilm, 3 PilihLokasi, 3 PilihJamTayang, 3 PilihKursi, 3 ProsesPembayaran

check FilmSelectionValid for 5 but exactly 3 User, 5 Film, 3 Location, 5 Showtime, 20 Seat, 2 Login, 3 PilihFilm, 3 PilihLokasi, 3 PilihJamTayang, 3 PilihKursi, 3 ProsesPembayaran

check LokasiSelectionValid for 5 but exactly 3 User, 5 Film, 3 Location, 5 Showtime, 20 Seat, 2 Login, 3 PilihFilm, 3 PilihLokasi, 3 PilihJamTayang, 3 PilihKursi, 3 ProsesPembayaran

check PembayaranValid for 5 but exactly 3 User, 5 Film, 3 Location, 5 Showtime, 20 Seat, 2 Login, 3 PilihFilm, 3 PilihLokasi, 3 PilihJamTayang, 3 PilihKursi, 3 ProsesPembayaran

check KursiBookingValid for 5 but exactly 3 User, 5 Film, 3 Location, 5 Showtime, 20 Seat, 2 Login, 3 PilihFilm, 3 PilihLokasi, 3 PilihJamTayang, 3 PilihKursi, 3 ProsesPembayaran
