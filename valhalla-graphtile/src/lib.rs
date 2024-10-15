//! # Valhalla Graph Tile Manipulation
//!
//! This is an oxidized version of the graph tile access, manipulation and data structures
//! of Valhalla's `baldr` module.

// Private modules by default
mod graph_id;
mod graph_reader;
pub mod graph_tile;
pub mod tile_hierarchy;
pub mod tile_provider;

use enumset::{enum_set, EnumSet, EnumSetType};
use zerocopy_derive::TryFromBytes;
// Pub use for re-export without too many levels of hierarchy.
// The implementations are sufficiently complex that we want to have lots of files,
// But many of those only have one or two useful definitions to re-export,
// so this flattens things for better ergonomics.
pub use graph_id::GraphId;
pub use graph_reader::GraphReader;

/// Road class; broad hierarchies of relative (and sometimes locally specific) importance.
///
/// These are used in a variety of situations:
/// - For inferring access in the absence of explicit tags
/// - For estimating speeds when better data is not available
/// - To determine preference / avoidance for roads
#[repr(u8)]
pub enum RoadClass {
    Motorway,
    Trunk,
    Primary,
    Secondary,
    Tertiary,
    Unclassified,
    Residential,
    ServiceOther,
}

/// Sub-categorization of roads based on specialized usage.
#[derive(TryFromBytes, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum RoadUse {
    // General road-oriented tags
    /// Standard road (the default).
    Road = 0,
    /// Entrance or exit ramp.
    Ramp = 1,
    /// Turn lane
    TurnChannel = 2,
    /// Agricultural use, forest tracks, and some unspecified rough roads.
    Track = 3,
    /// Driveway or private service road.
    Driveway = 4,
    /// Service road with limited routing use.
    Alley = 5,
    /// Access roads in parking areas.
    ParkingAisle = 6,
    /// Emergency vehicles only.
    EmergencyAccess = 7,
    /// Commercial drive-thru (banks/fast-food are common examples).
    DriveThru = 8,
    /// A Cul-de-sac (edge that forms a loop and is only connected at one node to another edge;
    /// common in some subdivisions).
    CulDeSac = 9,
    /// Streets with preference towards bicyclists and pedestrians.
    LivingStreet = 10,
    /// A generic service road (not specifically a driveway, alley, parking aisle, etc.).
    ServiceRoad = 11,

    // Bicycle-specific uses
    /// A dedicated bicycle path.
    Cycleway = 20,
    /// A mountain bike trail.
    MountainBike = 21,

    /// A sidewalk along another road (usually designated for pedestrian use; cycle policies vary)
    Sidewalk = 24,

    // Pedestrian-specific uses
    /// A type of road with pedestrian priority; bicycles may be granted access in some cases.
    Footway = 25,
    /// A stairway/steps.
    Steps = 26,
    Path = 27,
    Pedestrian = 28,
    Bridleway = 29,
    /// A crosswalk or other designated crossing.
    PedestrianCrossing = 32,
    Elevator = 33,
    Escalator = 34,
    Platform = 35,

    // Rest/Service Areas
    RestArea = 30,
    ServiceArea = 31,

    /// Other... currently, either BSS Connection or unspecified service road
    Other = 40,

    // Ferry and rail ferry
    Ferry = 41,
    RailFerry = 42,

    /// Roads currently under construction
    Construction = 43,

    // Transit specific uses. Must be last in the list
    /// A rail line (subway, metro, train).
    Rail = 50,
    /// A bus line.
    Bus = 51,
    /// Connection egress <-> station
    EgressConnection = 52,
    /// Connection station <-> platform
    PlatformConnection = 53,
    /// Connection osm <-> egress
    TransitConnection = 54,
    // WARNING: This is a 6-bit field, so never add a value higher than 63!
}

/// Access permission by travel type.
///
/// This is stored internally as a bit field.
/// NOTE: While it is a 16-bit integer, the way it is stored in directed edges
/// only allows for TWELVE bits to be used!
#[derive(Debug, EnumSetType)]
#[enumset(repr = "u16")]
pub enum Access {
    Auto,
    Pedestrian,
    Bicycle,
    Truck,
    Emergency,
    Taxi,
    Bus,
    HOV,
    Wheelchair,
    Moped,
    Motorcycle,
    GolfCart,
    // NOTE: Only 12 bits are allowed to be used, so this enum cannot contain any more variants!
    // All = 4095,
}

pub const VEHICULAR_ACCESS: EnumSet<Access> = enum_set!(
    Access::Auto
        | Access::Truck
        | Access::Moped
        | Access::Motorcycle
        | Access::Taxi
        | Access::Bus
        | Access::HOV
        | Access::GolfCart
);

/// The number of subdivisions in each graph tile
const BIN_COUNT: u8 = 25;

#[cfg(test)]
mod tests {
    use crate::Access;
    use enumset::EnumSet;

    #[test]
    fn test_access_representation() {
        let set: EnumSet<Access> = EnumSet::from_repr(2048);
        assert_eq!(set.len(), 1);
        assert!(set.contains(Access::GolfCart));
    }

    #[test]
    fn test_all_access_representation() {
        let set: EnumSet<Access> = EnumSet::all();
        assert_eq!(set.len(), 12);
        assert_eq!(set.as_repr(), 4095);
    }
}
