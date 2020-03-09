class {:autocontracts} CarPark {

    // Log messages
    const debug := true;

    // Total car park size
    const carParkSize: int;

    // Minimum number of empty spaces - set to 5 in constructor
    const minEmptySpaces:= 5;

    // Number of reserved spaces - 0 by default
    const reservedSpacesSize: int; // int

    // The current number of subscriptions
    var currentSubscriptionCount : int

    // Array of vehicle registrations with subscription
    var subscriptionRegistrations: array<int>;

    // If reserved parking in force, true by default
    var reservedParkingInForce: bool;
    
    // IDs of public available spaces
    var availableSpaces: set<int>;

    // IDs of reserved spaces
    var reservedSpaces: set<int>;
    
    // IDs of in use spaces
    var inUseSpaces: set<int>;

    // Set car park size
    constructor (carParkSize: int, reservedSpacesSize: int)
    // Ensure some reserved spaces, and that total size is bigger than reserved
    requires 0 < reservedSpacesSize < carParkSize;
    // Ensure total car park size is bigger than reserved spaced + the minimum 5 empty spaces
    requires 5 + reservedSpacesSize < carParkSize;
    // Ensure initial allocation is 0
    ensures |inUseSpaces| == 0; 
    // Ensure reservedSpaces set cardinal matches given param
    // ensures |reservedSpaces| == reservedSpacesSize; 
    // Ensure availableSpaces set cardinal equal to overall size - reserved spaces
    // ensures |availableSpaces| == carParkSize - reservedSpacesSize;
    {
        this.carParkSize:= carParkSize;
        this.reservedSpacesSize:= reservedSpacesSize;
        this.subscriptionRegistrations:= new int[reservedSpacesSize];
        this.currentSubscriptionCount:= 0;
        this.reservedParkingInForce:= true;
        this.inUseSpaces:= {};
        this.reservedSpaces:= {};
        this.availableSpaces:= {};

        // Initialise sets with comprehension expression
        this.reservedSpaces:= set x: int | 0 <= x < reservedSpacesSize;
        this.availableSpaces:= set x: int | reservedSpacesSize <= x < carParkSize;
    }

    method printSets()
    {
        print "inUseSpaces: ", this.inUseSpaces, "\n";
        print "reservedSpaces: ", this.reservedSpaces, "\n";
        print "availableSpaces: ", this.availableSpaces, "\n";
    }

    method enterCarPark() returns (spaceId: int, success: bool)
    modifies this;
    // Success should be false if not enough spaces
    ensures old(|availableSpaces|) <= minEmptySpaces ==> !success;
    // If success:
    // check old set + plus new value match new set to verify no other changes
    ensures success ==> old(inUseSpaces) + {spaceId} == inUseSpaces;
    // Check old set matches new set minus spaceID to verify no other changes
    ensures success ==> old(availableSpaces) == availableSpaces + {spaceId};
    // Check reserved set not changed regardless
    ensures old(reservedSpaces) == reservedSpaces;
    // autocontract ensures spaceId doesn't exist in more than one set
    {
        // Check if enough empty spaces or return early
        if |availableSpaces| <= minEmptySpaces
        {
            spaceId := -1;
            success := false;
            if debug { print "enterCarPark - availableSpaces less than minEmptySpaces \n"; }
            return;
        }

        // Get an arbitrary id and set success
        spaceId :| spaceId in availableSpaces;
        success := true;

        // Remove spaceId from availableSpaces and add to inUseSpaces
        availableSpaces := availableSpaces - {spaceId};
        inUseSpaces := inUseSpaces + {spaceId};

        if debug { print "enterCarPark - space ", spaceId, "\n"; }

    } 

    method leaveCarPark(spaceId: int) returns (success: bool)
    modifies this;
    // If no success:
    // If spaceId not in old inUse, then should have failed
    ensures spaceId !in old(inUseSpaces) ==> !success;
    // All sets should remain the same
    ensures !success ==> old(inUseSpaces) == inUseSpaces && old(availableSpaces) == availableSpaces && old(reservedSpaces) == reservedSpaces;
    // If success:
    // If success, spaceId should be in old inUseSpaces
    ensures success ==> spaceId in old(inUseSpaces);
    // If success, check inUseSpaces only differs by spaceId
    ensures success ==> old(inUseSpaces) == inUseSpaces + {spaceId};
    // If spaceId was reserved space and reservedInForce, spaceId should now be in reservedSpaces with no other changes
    ensures success && reservedParkingInForce && spaceId < reservedSpacesSize ==> old(reservedSpaces) + {spaceId} == reservedSpaces;
    // If spaceId was not in reserved space, or reservedNotInForce, should now be in availableSpaces with no other changes
    ensures success && ((spaceId > reservedSpacesSize) || !reservedParkingInForce) ==> old(availableSpaces) + {spaceId} == availableSpaces;
    // Precontract enforces correct set length and no duplication
    {
        // If not inUse, fail early
        if (spaceId !in inUseSpaces) 
        {
            success := false;
            if debug { print "leaveCarPark(",spaceId,") - failed, spaceId not in use\n"; }
            return;
        }

        success := true;
        inUseSpaces := inUseSpaces - {spaceId};
        if debug { print "leaveCarPark(",spaceId,") - success\n"; }

        // Check if weekend parking and early return
        if (!reservedParkingInForce)
        {
            availableSpaces := availableSpaces + {spaceId};
            return;
        }

        // Check if space should be returned to reserved parking or not
        if (spaceId < reservedSpacesSize)
        {
            reservedSpaces := reservedSpaces + {spaceId};
        }
        else
        {
            availableSpaces := availableSpaces + {spaceId};
        }
    }

    function checkAvailability(): int
    {
       |availableSpaces| - minEmptySpaces
    }

    method enterReservedCarPark(registration: int) returns (spaceId: int, success: bool) 
    // ensures reservedParkingInForce && spaceId !in registered ==> spaceId == -1 && !success
    // ensures reservedParkingInForce && spaceId in registered ==> 0 <= spaceId && success;
    // ensures !reservedParkingInForce 
    {

        // if reservedParkingInForce && registration not in subscriptionRegistrations
        //      return fail (-1);

        // if reserved parkingInForce && registration in subscriptionRegistrations
        //      spaceId = reservedSpaces.random
        //      reservedSpaces - spaceId
        //      inUseSpaces + spaceId
        //      return spaceId

        // if !parkingInForce
        //      spaceId = availableSpaces.random
        //      availableSpaces - spaceId
        //      inUseSpaces + spaceId
        //      return spaceId

    }

    method makeSubscription(registration: int) {
        // Check space available
        // if subscriptionCount => reservedSpacesSize
        //      return false (fail?)

        // subscriptionRegistrations[subscriptionCount] = registration
        // subscriptionCount++
        // return true
    }

    method openReservedArea() {
        // reservedParkingInForce = false;
        // availableSpaces + reservedSpaces
        // reservedSpaces = {}

    }

    method closeCarPark() {
        // carsDestroyed = |inUseSpaces|
        // Reset state
        // inUseSpaces = {}
        // reservedSpaces = {1...numberOfReservedSpaces}
        // availableSpaces = {(numberOfReservedSpaces + 1) ... carParkSize}
        // return carsDestroyed
    }

    // For overall car park state
    predicate valid()
    {
        // Ensure no values appear in both given sets
        availableSpaces * inUseSpaces == {} &&
        reservedSpaces * inUseSpaces == {} &&
        availableSpaces * reservedSpaces == {} && 
        // Ensure total size of sets == overall car park size
        |availableSpaces| + |inUseSpaces| + |reservedSpaces| == carParkSize &&
        // Ensure carpark has size
        carParkSize > 0 &&
        minEmptySpaces > 0 &&
        // Ensure all values in sets are within 1 to carParkSize
        forall i :: i in availableSpaces ==> 0 <= i < carParkSize &&
        forall i :: i in reservedSpaces ==> 0 <= i < carParkSize &&
        forall i :: i in inUseSpaces ==> 0 <= i < carParkSize
    }


    // Needs setting to read only ??
    method printStatus()
    {
        var output := "";

        // for loop (i in carParkSize)
        // if availableSpaces.has(i) {output = output + i + "A  "}
        // if reservedSpaces.has(i) {output = output + i + "R  "}
        // if inUseSpaces.has(i) {output = output + i + "X  "}

        // total available reserved = |reservedSpaces|
        // total available public = |availableSpaces|
        // total spaces in use = |inUseSpaces|
        
    }
}

method Main()
{
    var carParkSize := 15;
    var reservedSpaces := 5;
    var cp := new CarPark(carParkSize, reservedSpaces);
    cp.printSets();

    var id1, success1 := cp.enterCarPark();
    var id2, success2 := cp.enterCarPark();
    var id3, success3 := cp.enterCarPark();
    var id4, success4 := cp.enterCarPark();
    var id5, success5 := cp.enterCarPark();
    var id6, success6 := cp.enterCarPark();

    cp.printSets();     

    var leaveSuccess := cp.leaveCarPark(id1);
  

    cp.printSets();

}