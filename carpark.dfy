class {:valid} CarPark {

    // Total car park size
    var carParkSize: int;

    // Minimum number of empty spaces - set to 5 in constructor
    var minEmptySpaces: int;

    // Number of reserved spaces - 0 by default
    var reservedSpacesSize: int; // int

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
    // Ensure has value and not negative
    requires carParkSize > 0;
    // Ensure not negative
    requires reservedSpacesSize >= 0;
    // Ensure not going to reserve more spaces than exist
    requires reservedSpacesSize <= carParkSize; 
    // Ensure initial allocation is 0
    ensures |inUseSpaces| == 0; 
    // Ensure reservedSpaces set cardinal matches given param
    // ensures |reservedSpaces| == reservedSpacesSize; 
    // Ensure availableSpaces set cardinal equal to overall size - reserved spaces
    // ensures |availableSpaces| == carParkSize - reservedSpacesSize;
    {
        this.carParkSize:= carParkSize;
        this.reservedSpacesSize:= reservedSpacesSize;
        this.minEmptySpaces:= 5;
        this.subscriptionRegistrations:= new int[reservedSpacesSize];
        this.currentSubscriptionCount:= 0;
        this.reservedParkingInForce:= true;
        this.inUseSpaces:= {};
        this.reservedSpaces:= {};
        this.availableSpaces:= {};

        // Initialise sets with comprehension expression
        this.reservedSpaces:= set x: int | 0 < x <= reservedSpacesSize;
        this.availableSpaces:= set x: int | reservedSpacesSize < x <= carParkSize;
        
    }

    method printSets()
    {
        print "inUseSpaces: ", this.inUseSpaces, "\n";
        print "reservedSpaces: ", this.reservedSpaces, "\n";
        print "availableSpaces: ", this.availableSpaces, "\n";
    }
    method enterCarPark() returns (spaceId: int, success: bool)
    modifies this;
    requires valid();
    // If not enough spaces, success should be false
    ensures old(|availableSpaces|) <= minEmptySpaces ==> !success;
    // If success, check spaceId is in inUseSpaces, old availableSpaces, and no longer in availableSpaces
    ensures success ==> spaceId in inUseSpaces;
    ensures success ==> spaceId !in availableSpaces;
    ensures success ==> spaceId in old(availableSpaces);
    
    // Check spaceId is within range 1-CarParkSize
    // ensures success ==> 0 < spaceId <= carParkSize;
    {
        // Check if enough empty spaces or return early
        if |availableSpaces| <= minEmptySpaces
        {
            spaceId := -1;
            success := false;
            return;
        }

        // Get an arbitrary id and set success
        spaceId :| spaceId in availableSpaces;
        success := true;

        // Remove spaceId from availableSpaces and add to inUseSpaces
        availableSpaces := availableSpaces - {spaceId};
        inUseSpaces := inUseSpaces + {spaceId};

    } 

    method leaveCarPark(spaceId: int) 
    {
        // Take space number as input param
        // availableSpaces - spaceId
        // if (spaceId <= reservedSpacesSize ) 
        //      reservedSpaces + spaceId
        // else
        //      availableSpaces + spaceId
    }

    // Should be a function - won't change anything, just return value
    method checkAvailability() // : int
    {
        // return |availableSpaces|
    }

    method enterReservedCarPark(registration: int) {

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
    reads this;
    {
        // Ensure no values appear in both given sets
        availableSpaces * inUseSpaces == {} &&
        reservedSpaces * inUseSpaces == {} &&
        availableSpaces * reservedSpaces == {} && 
        // Ensure total size of sets == overall car park size
        |availableSpaces| + |inUseSpaces| + |reservedSpaces| == carParkSize &&
        // Ensure carpark has size
        carParkSize > 0 &&
        minEmptySpaces > 0
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
    var carParkSize := 10;
    var reservedSpaces := 5;
    var cp := new CarPark(carParkSize, reservedSpaces);
    cp.printSets();

}