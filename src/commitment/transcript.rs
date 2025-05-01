//! Declares a series of transcript types for Merlin transcripts.
//! WARNING: This trait differs slightly from how Merlin defines the same traits. Essentially, rather than
//! re-instantiating this type for each different point type that we use, we simply traffic bytes in and out for e.g
//! appending points or producing challenges. It is the responsibility of the caller to realise this functionality.

use merlin::Transcript;

pub const CHALLENGE_SIZE: usize = 32;


pub trait GKMemberTranscript {
    /// Append a domain separator.
    fn domain_sep(&mut self);

    /// Append a point.
    fn append_point(&mut self, label: &'static [u8], point: &[u8]);

    /// Produce the challenge.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE];
}

impl GKMemberTranscript for Transcript {
    fn domain_sep(&mut self) {
        self.append_message(b"dom-sep", b"gk-member-proof");
    }

    fn append_point(&mut self, label: &'static [u8], point: &[u8]) {
        self.append_message(label, point);
    }

    // fn append_points(&mut self, label: &'static [u8], points: &[Projective]) {
    //     for (i, point) in points.iter().enumerate() {
    //         let point_label = format!("{}{}", std::str::from_utf8(label).unwrap(), i).as_bytes();
    //         self.append_bytes(point_label, point.as_bytes());
    //     }
    // }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> [u8; CHALLENGE_SIZE] {
        let mut buf = [0u8; CHALLENGE_SIZE];
        self.challenge_bytes(label, &mut buf);
        buf
    }
}

