open util/boolean

sig String {}

abstract sig User {
    username: String,
    password: String,
    ticket: lone Ticket
}

sig Login {
    username: String,
    password: String
}

abstract sig Pilih {
    chosen: lone User,
    available: lone Location
}

sig PilihFilm extends Pilih {
    availableFilm: lone Film
}

sig PilihLokasi extends Pilih {
    availableLocations: lone Location
}

sig PilihJamTayang extends Pilih {
    availableShowtimes: lone Showtime
}

sig PilihKursi extends Pilih {
    availableSeats: lone Seat
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
    time: Int
}

sig Seat {
    seatNumber: String,
    isOccupied: Bool
}

sig Ticket {}

fact UserLogin {
    all u: User | u in Login
}

fact UserChooseFilm {
    all pf: PilihFilm | pf.chosen in User and pf.availableFilm in Film
}

fact UserChooseLocation {
    all pl: PilihLokasi | pl.chosen in User and pl.available in Location
}

fact UserChooseShowtime {
    all pt: PilihJamTayang | pt.chosen in User and pt.availableShowtimes in Showtime
}

fact UserChooseSeat {
    all pk: PilihKursi | pk.chosen in User and pk.availableSeats in Seat
}

fact ProsesPembayaranFacts {
    all pp: ProsesPembayaran | pp in User and pp.paymentDetails in String
}

fact TicketFacts {
    all t: Ticket | lone t
}

pred verifyLogin(username: String, password: String) {
    some u: User | u.username = username and u.password = password
}

pred main() {
    some u: User, lf: Login, pf: PilihFilm, pl: PilihLokasi, pt: PilihJamTayang, pk: PilihKursi, pp: ProsesPembayaran |
        u in lf and u in pf.chosen and u in pl.chosen and u in pt.chosen and u in pk.chosen and u in pp and
        verifyLogin[lf.username, lf.password] and
        pf.available in pl.available and pl.available in pt.available and pt.available in pk.available and
        pk.available in pp and pp in pf.chosen.ticket
}

assert systemWorks {
    all u: User | u in User implies some main()
}

run systemWorks for 5
check main for 5

