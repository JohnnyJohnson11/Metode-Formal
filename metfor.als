open util/integer
open util/date

sig User {
  username: String,
  password: String,
  selectedFilm: lone Film,
  selectedLocation: lone Location,
  selectedShowtime: lone Showtime,
  selectedSeat: lone Seat,
  paymentProcess: one ProsesPembayaran,
  ticket: lone Ticket
}

sig Login {
  username: String,
  password: String
}

sig PilihFilm {
  availableFilm: set Film,
  selectedFilm: lone Film
}

sig PilihLokasi {
  availableLocations: set Location,
  selectedLocation: lone Location
}

sig PilihJamTayang {
  availableShowtimes: set Showtime,
  selectedShowtime: lone Showtime
}

sig PilihKursi {
  availableSeats: set Seat,
  selectedSeat: lone Seat
}

sig ProsesPembayaran {
  paymentDetails: String
}

sig Film {
  title: String,
  duration: Int,
  genre: String
}

sig Location {
  name: String,
  address: String
}

sig Showtime {
  time: DateTime
}

sig Seat {
  seatNumber: String,
  isOccupied: Bool
}

sig Ticket {}

-- Associations and Aggregations
fact Associations {
  all u: User |
    u.selectedFilm in PilihFilm.selectedFilm and
    u.selectedLocation in PilihLokasi.selectedLocation and
    u.selectedShowtime in PilihJamTayang.selectedShowtime and
    u.selectedSeat in PilihKursi.selectedSeat and
    u.paymentProcess = ProsesPembayaran and
    u.ticket in Ticket
}

-- Constraints
fact TicketConstraints {
  all t: Ticket | some s: Seat | t in s
}

-- Sequence Diagram Constraints
fact SequenceConstraints {
  all u: User |
    (u in Login.username and u in Login.password) =>
      (some pf: PilihFilm | u.selectedFilm in pf.selectedFilm)
}

-- Activity Constraints
fact ActivityConstraints {
  all u: User |
    u.selectedFilm != none and u.selectedLocation != none and u.selectedSeat != none =>
      (u.selectedFilm in PilihFilm.selectedFilm and
      u.selectedLocation in PilihLokasi.selectedLocation and
      u.selectedSeat in PilihKursi.selectedSeat)
}

-- Predicates
pred loginGagal(u: User, l: Login) {
  (l.username - u.username) or (l.password - u.password)
}

pred kursiGagalBooking(u: User, pk: PilihKursi) {
  some s: Seat | s.isOccupied = true and s not in pk.selectedSeat
}

-- Assertions
assert LoginGagalAssertion {
  all u: User, l: Login | loginGagal[u, l] implies l not in u
}

assert KursiGagalBookingAssertion {
  all u: User, pk: PilihKursi | kursiGagalBooking[u, pk] implies pk.selectedSeat != u.selectedSeat
}

run loginGagal for 5 User, 3 Login
run kursiGagalBooking for 5 User, 5 PilihKursi
